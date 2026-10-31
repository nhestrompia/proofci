import { test } from 'node:test';
import assert from 'node:assert/strict';
import { assessEnforcement } from '../src/enforcement.ts';

const expected = { strict: true, checks: [{ context: 'ProofCI', app_id: 7 }] };
test('classifies the observed branch configuration without claiming active verification', () => {
  assert.equal(assessEnforcement({ appId: 7, protection: { required_status_checks: expected, enforce_admins: { enabled: true } }, rules: [] }), 'confirmed');
  assert.equal(assessEnforcement({ appId: 7, protection: { required_status_checks: { strict: true, checks: [{ context: 'ProofCI', app_id: 8 }] }, enforce_admins: { enabled: true } }, rules: [] }), 'misconfigured');
  assert.equal(assessEnforcement({ appId: 7, protection: { required_status_checks: expected, enforce_admins: { enabled: false } }, rules: [] }), 'unconfirmed');
  assert.equal(assessEnforcement({ appId: 7, protection: null, rules: [] }), 'unconfirmed');
  assert.equal(assessEnforcement({ appId: 7, protection: { required_status_checks: null }, rules: [{ type: 'required_status_checks' }] }), 'unconfirmed');
});
