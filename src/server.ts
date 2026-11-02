import { startControl } from './control.ts';

const control = await startControl(process.env);
for (const signal of ['SIGTERM', 'SIGINT'] as const) process.once(signal, () => { void control.stop(); });
