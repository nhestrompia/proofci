export type Enforcement = 'confirmed' | 'misconfigured' | 'unconfirmed';
function object(value: unknown): value is Record<string, unknown> { return typeof value === 'object' && value !== null && !Array.isArray(value); }

/** Assesses only complete legacy-branch-protection evidence; rulesets require further inspection. */
export function assessEnforcement(input: { appId: number; protection: unknown; rules: unknown }): Enforcement {
  if (!object(input.protection) || !Array.isArray(input.rules) || input.rules.length >= 100 || input.rules.some(rule => !object(rule) || typeof rule.type !== 'string')) return 'unconfirmed';
  const status = input.protection.required_status_checks;
  const rulesMaySupplyCheck = input.rules.some(rule => object(rule) && (rule.type === 'required_status_checks' || rule.type === 'merge_queue'));
  if (status === null) return rulesMaySupplyCheck ? 'unconfirmed' : 'misconfigured';
  if (!object(status) || typeof status.strict !== 'boolean' || !Array.isArray(status.checks)) return 'unconfirmed';
  if (status.checks.some(check => !object(check) || typeof check.context !== 'string' || (check.app_id !== null && typeof check.app_id !== 'number'))) return 'unconfirmed';
  const expected = status.checks.some(check => object(check) && check.context === 'ProofCI' && check.app_id === input.appId);
  if ((!expected || !status.strict) && !rulesMaySupplyCheck) return 'misconfigured';
  if (!expected || !status.strict) return 'unconfirmed';
  const admins = input.protection.enforce_admins;
  if (!object(admins) || admins.enabled !== true) return 'unconfirmed';
  return 'confirmed';
}
