"""Budget and authorize requests before they reach a trusted model provider.

This module belongs in the credential-holding control process, not the proof
container. Provider adapters are trusted deployment code, never repository code.
"""
from dataclasses import dataclass
import hashlib
import json
import multiprocessing
import threading
import time


class AuthorizationDenied(PermissionError):
    pass


class BudgetExhausted(ValueError):
    pass


@dataclass(frozen=True)
class Limits:
    context_bytes: int
    input_tokens: int
    output_tokens: int
    cost_micros: int
    input_micros_per_million: int
    output_micros_per_million: int
    max_output_per_call: int

    def __post_init__(self):
        if any(type(value) is not int or value <= 0 for value in vars(self).values()):
            raise ValueError("broker limits must be positive integers")


def _cost(tokens, rate):
    return (tokens * rate + 999_999) // 1_000_000


def _invoke(provider, request, output, pipe):
    try:
        result = provider(request, output)
        if (not isinstance(result, dict) or not isinstance(result.get("body"), str)
                or len(result["body"].encode()) > 65536):
            raise ValueError("invalid provider response")
        pipe.send(("ok", result))
    except BaseException as error:
        pipe.send(("error", type(error).__name__))
    finally:
        pipe.close()


class Broker:
    def __init__(self, *, run_id, repository, private, consent, authorize, limits, provider,
                 run_deadline):
        if not run_id or not repository:
            raise ValueError("run and repository identities are required")
        self.run_id = run_id
        self.repository = repository
        self.private = private
        self.consent = consent
        self.authorize = authorize
        self.limits = limits
        self.provider = provider
        self.deadline = min(run_deadline, time.monotonic() + 900)
        self.events = []
        self.input_tokens = 0
        self.output_tokens = 0
        self.cost_micros = 0
        self.attempts = {}
        self.obligation_deadlines = {}
        self._lock = threading.Lock()
        self._deadline_lock = threading.Lock()
        self._transition_sink = None

    def set_transition_sink(self, sink):
        if self.events:
            raise ValueError("cannot change accounting after a request")
        self._transition_sink = sink

    def _record(self, event):
        if self._transition_sink is not None:
            self._transition_sink(event)
        self.events.append(event)

    def request(self, *, repository, obligation, candidate, contract, diagnostic, deadline):
        if not isinstance(obligation, str) or not obligation:
            raise ValueError("invalid obligation identity")
        with self._deadline_lock:
            obligation_deadline = self.obligation_deadlines.setdefault(obligation, time.monotonic() + 120)
        deadline = min(deadline, self.deadline, obligation_deadline)
        wait = max(0, deadline - time.monotonic())
        if not self._lock.acquire(timeout=wait):
            raise TimeoutError("request deadline expired")
        try:
            return self._request(repository=repository, obligation=obligation, candidate=candidate,
                                 contract=contract, diagnostic=diagnostic, deadline=deadline)
        finally:
            self._lock.release()

    def _request(self, *, repository, obligation, candidate, contract, diagnostic, deadline):
        if time.monotonic() >= deadline:
            raise TimeoutError("request deadline expired")
        if (repository != self.repository or
                not self.authorize(repository, self.run_id, obligation, candidate, contract, deadline)):
            raise AuthorizationDenied("repository request is not authorized")
        if self.private and not self.consent(repository):
            raise AuthorizationDenied("private source transmission is disabled")
        if self.provider is None or not getattr(self.provider, "available", True):
            raise RuntimeError("provider is unavailable")
        count = self.attempts.get(obligation, 0)
        if count >= 5:
            raise BudgetExhausted("attempt limit exhausted")
        if time.monotonic() >= deadline:
            raise TimeoutError("request deadline expired")
        request = {"candidate": candidate, "contract": contract, "diagnostic": diagnostic}
        raw = json.dumps(request, ensure_ascii=False, separators=(",", ":")).encode()
        # Reserve framing and the fixed provider instruction as well as the data.
        reserved_in = len(raw) + 4096
        if reserved_in > self.limits.context_bytes:
            raise BudgetExhausted("context limit exhausted")
        reserved_out = self.limits.max_output_per_call
        reserved_cost = (_cost(reserved_in, self.limits.input_micros_per_million)
                         + _cost(reserved_out, self.limits.output_micros_per_million))
        if (self.input_tokens + reserved_in > self.limits.input_tokens or
            self.output_tokens + reserved_out > self.limits.output_tokens or
            self.cost_micros + reserved_cost > self.limits.cost_micros):
            raise BudgetExhausted("model budget exhausted")
        attempt = count + 1
        request_id = hashlib.sha256(json.dumps([self.run_id, repository, obligation, attempt],
                                               separators=(",", ":")).encode()).hexdigest()
        self.attempts[obligation] = attempt
        self.input_tokens += reserved_in
        self.output_tokens += reserved_out
        self.cost_micros += reserved_cost
        identity = {"request_id": request_id, "run_id": self.run_id, "repository": repository,
                    "obligation": obligation, "attempt": attempt}
        self._record({**identity, "state": "reserved", "input_tokens": reserved_in,
                      "output_tokens": reserved_out, "cost_micros": reserved_cost})
        receiver = sender = process = None
        try:
            ctx = multiprocessing.get_context("fork")
            receiver, sender = ctx.Pipe(duplex=False)
            process = ctx.Process(target=_invoke, args=(self.provider, request, reserved_out, sender))
            process.start()
            sender.close()
            if not receiver.poll(max(0, deadline - time.monotonic())):
                raise TimeoutError("provider timed out")
            try:
                state, response = receiver.recv()
            except EOFError as error:
                raise RuntimeError("provider exited without a response") from error
            if state != "ok":
                raise RuntimeError("provider request failed: " + response)
            if (not isinstance(response, dict) or set(response) != {"body", "input_tokens", "output_tokens"}
                or not isinstance(response["body"], str)
                or type(response["input_tokens"]) is not int or type(response["output_tokens"]) is not int
                or not 0 <= response["input_tokens"] <= reserved_in
                or not 0 <= response["output_tokens"] <= reserved_out
                or len(response["body"].encode()) > 65536):
                raise RuntimeError("invalid provider response")
            actual_cost = (_cost(response["input_tokens"], self.limits.input_micros_per_million)
                           + _cost(response["output_tokens"], self.limits.output_micros_per_million))
            self._record({**identity, "state": "settled", "input_tokens": response["input_tokens"],
                          "output_tokens": response["output_tokens"], "cost_micros": actual_cost})
            self.input_tokens -= reserved_in - response["input_tokens"]
            self.output_tokens -= reserved_out - response["output_tokens"]
            self.cost_micros -= reserved_cost - actual_cost
            return request_id, response["body"]
        except BaseException:
            self._record({**identity, "state": "uncertain", "input_tokens": reserved_in,
                          "output_tokens": reserved_out, "cost_micros": reserved_cost})
            raise
        finally:
            if sender is not None:
                sender.close()
            if receiver is not None:
                receiver.close()
            if process is not None:
                if process.is_alive():
                    process.kill()
                if process.pid is not None:
                    process.join()
