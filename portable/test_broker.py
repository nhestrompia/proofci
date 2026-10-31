import time
import unittest
from unittest.mock import patch

from broker import Broker, Limits


def good_provider(request, maximum):
    return {"body": "rfl", "input_tokens": 10, "output_tokens": 1}


def failed_provider(request, maximum):
    raise RuntimeError("provider unavailable")


def slow_provider(request, maximum):
    time.sleep(5)


class BrokerTests(unittest.TestCase):
    def broker(self, **overrides):
        options = dict(run_id="run", repository="repo", private=False,
                       consent=lambda _: False, authorize=lambda repo, run, obligation, candidate, contract, deadline: True,
                       limits=Limits(8192, 50000, 1000, 50000, 1000000, 1000000, 100),
                       provider=good_provider, run_deadline=time.monotonic() + 30)
        options.update(overrides)
        return Broker(**options)

    def request(self, broker, repository="repo"):
        return broker.request(repository=repository, obligation="property", candidate="target",
                              contract="statement", diagnostic="unproven", deadline=time.monotonic() + 10)

    def test_private_source_requires_repository_consent(self):
        broker = self.broker(private=True)
        with self.assertRaises(PermissionError):
            self.request(broker)
        self.assertEqual(broker.events, [])

    def test_repository_authorization_is_checked_before_request(self):
        broker = self.broker()
        with self.assertRaises(PermissionError):
            self.request(broker, "another")
        self.assertEqual(broker.events, [])

    def test_other_repository_context_is_not_sent(self):
        broker = self.broker(authorize=lambda repo, run, obligation, candidate, contract, deadline:
                             candidate == "approved" and contract == "statement")
        with self.assertRaises(PermissionError):
            self.request(broker)
        self.assertEqual(broker.events, [])

    def test_budget_is_reserved_before_dispatch(self):
        limits = Limits(8192, 100, 1000, 50000, 1000000, 1000000, 100)
        broker = self.broker(limits=limits)
        with self.assertRaisesRegex(ValueError, "budget"):
            self.request(broker)
        self.assertEqual(broker.events, [])

    def test_context_limit_is_checked_before_dispatch(self):
        limits = Limits(4096, 50000, 1000, 50000, 1000000, 1000000, 100)
        broker = self.broker(limits=limits)
        with self.assertRaisesRegex(ValueError, "context"):
            self.request(broker)
        self.assertEqual(broker.events, [])

    def test_cost_limit_is_checked_before_dispatch(self):
        limits = Limits(8192, 50000, 1000, 1, 1000000, 1000000, 100)
        broker = self.broker(limits=limits)
        with self.assertRaisesRegex(ValueError, "budget"):
            self.request(broker)
        self.assertEqual(broker.events, [])

    def test_timeout_retains_reservation(self):
        broker = self.broker(provider=slow_provider)
        with self.assertRaises(TimeoutError):
            broker.request(repository="repo", obligation="property", candidate="target", contract="statement",
                           diagnostic="unproven", deadline=time.monotonic() + 0.1)
        self.assertEqual(broker.events[-1]["state"], "uncertain")
        self.assertEqual(broker.output_tokens, 100)

    def test_process_setup_failure_records_uncertain_reservation(self):
        broker = self.broker()
        with patch("broker.multiprocessing.get_context", side_effect=OSError("unavailable")):
            with self.assertRaises(OSError):
                self.request(broker)
        self.assertEqual([event["state"] for event in broker.events], ["reserved", "uncertain"])

    def test_journal_failure_prevents_provider_dispatch(self):
        broker = self.broker()
        def fail(_event):
            raise OSError("journal unavailable")
        broker.set_transition_sink(fail)
        with self.assertRaises(OSError):
            self.request(broker)
        self.assertEqual(broker.events, [])

    def test_success_records_settled_usage_and_stable_request_identity(self):
        broker = self.broker()
        identity, body = self.request(broker)
        self.assertEqual(body, "rfl")
        self.assertEqual([event["state"] for event in broker.events], ["reserved", "settled"])
        self.assertEqual(broker.events[-1]["request_id"], identity)
        self.assertEqual((broker.input_tokens, broker.output_tokens, broker.cost_micros), (10, 1, 11))

    def test_failure_keeps_reserved_usage_and_stops_after_five_attempts(self):
        broker = self.broker(provider=failed_provider)
        for _ in range(5):
            with self.assertRaises(RuntimeError):
                self.request(broker)
        with self.assertRaisesRegex(ValueError, "attempt limit"):
            self.request(broker)
        self.assertEqual([event["state"] for event in broker.events][1::2], ["uncertain"] * 5)
        self.assertEqual(broker.output_tokens, 500)


if __name__ == "__main__":
    unittest.main()
