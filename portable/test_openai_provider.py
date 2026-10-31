import json
import unittest
from unittest.mock import patch

from openai_provider import OpenAIProvider


class Response:
    status = 200

    def read(self, limit):
        return json.dumps({"choices": [{"finish_reason": "stop", "message": {"content": "rfl"}}],
                           "usage": {"prompt_tokens": 12, "completion_tokens": 2}}).encode()


class Connection:
    def __init__(self, host, timeout):
        self.host = host
        self.timeout = timeout
        self.sent = None

    def request(self, method, path, body, headers):
        self.sent = (method, path, json.loads(body), headers)

    def getresponse(self):
        return Response()

    def close(self):
        pass


class ProviderTests(unittest.TestCase):
    def test_provider_uses_fixed_endpoint_without_model_tools(self):
        connections = []
        def connect(host, timeout):
            connection = Connection(host, timeout)
            connections.append(connection)
            return connection
        with patch("openai_provider.http.client.HTTPSConnection", side_effect=connect):
            provider = OpenAIProvider(api_key="secret", model="gpt-4o-mini")
            result = provider({"candidate": "target", "contract": "statement", "diagnostic": "unproven"}, 100)
        self.assertEqual(result, {"body": "rfl", "input_tokens": 12, "output_tokens": 2})
        self.assertEqual(connections[0].host, "api.openai.com")
        method, path, payload, _ = connections[0].sent
        self.assertEqual((method, path), ("POST", "/v1/chat/completions"))
        self.assertNotIn("tools", payload)
        self.assertEqual(payload["max_completion_tokens"], 100)

    def test_search_models_are_not_available(self):
        provider = OpenAIProvider(api_key="secret", model="gpt-4o-search-preview")
        self.assertFalse(provider.available)
        with self.assertRaisesRegex(RuntimeError, "unavailable"):
            provider({}, 10)


if __name__ == "__main__":
    unittest.main()
