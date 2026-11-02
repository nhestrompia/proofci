"""Model provider credentials are read by the broker process from a protected file."""
import os
from pathlib import Path
import tempfile
import unittest

import assist


class ModelCredentialTest(unittest.TestCase):
    def test_file_rotation_and_validation(self):
        with tempfile.TemporaryDirectory() as temp:
            key = Path(temp) / "openai-key"
            key.write_text("sk-old\n")
            key.chmod(0o600)
            environ = {"PROOFCI_OPENAI_API_KEY_FILE": str(key), "PROOFCI_OPENAI_API_KEY": "ignored"}
            self.assertEqual(assist.model_api_key(environ), "sk-old")
            replacement = Path(temp) / "openai-key.new"
            replacement.write_text("sk-new\n")
            replacement.chmod(0o600)
            os.replace(replacement, key)
            self.assertEqual(assist.model_api_key(environ), "sk-new")
            key.chmod(0o622)
            with self.assertRaises(ValueError):
                assist.model_api_key(environ)
            key.chmod(0o600)
            with self.assertRaises(ValueError):
                assist.model_api_key({"PROOFCI_OPENAI_API_KEY_FILE": "relative/key"})
            link = Path(temp) / "link"
            link.symlink_to(key)
            with self.assertRaises(ValueError):
                assist.model_api_key({"PROOFCI_OPENAI_API_KEY_FILE": str(link)})
            self.assertEqual(assist.model_api_key({"PROOFCI_OPENAI_API_KEY": "sk-env"}), "sk-env")
            self.assertIsNone(assist.model_api_key({}))


if __name__ == "__main__":
    unittest.main()
