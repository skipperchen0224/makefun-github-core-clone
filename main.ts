// Entry: bind an ephemeral port, register it with the env, poll /done, exit 0.
// Lifecycle mirrors the kit starter (main.ts): the suite scores the server forge.ts builds,
// and the lifecycle is the harness's, not the contest's. Never bind 8080 — the env owns it.

import { createServer } from 'node:http';
import { createApp } from './forge.ts';

const ENV_URL = (process.env.MAKEFUN_ENV_URL ?? '').replace(/\/+$/, '');
if (ENV_URL === '') {
  process.stderr.write('[entry] MAKEFUN_ENV_URL is not set: there is no env to register with\n');
  process.exit(1);
}

/** How long one register or done request may take before it is abandoned and retried. */
const REQUEST_TIMEOUT_MS = 30_000;
/** The first wait between retries, and the longest. */
const RETRY_INITIAL_MS = 250;
const RETRY_MAX_MS = 2_000;

const sleep = (ms: number): Promise<void> => new Promise((resolve) => setTimeout(resolve, ms));

/** The wait after `attempt` failed requests: exponential from RETRY_INITIAL_MS, capped. */
function retryDelay(attempt: number): number {
  return Math.min(RETRY_MAX_MS, RETRY_INITIAL_MS * 2 ** Math.min(attempt, 8));
}

/**
 * POST the bound port until the env accepts it. 200 is the normal answer; 409 means a first register
 * already won, which is not this process's to fix. 400 and 405 are contract errors and end the program;
 * a network error or another status is retried, since the env may still be starting.
 */
async function register(port: number): Promise<void> {
  for (let attempt = 0; ; attempt += 1) {
    try {
      const res = await fetch(`${ENV_URL}/register`, {
        method: 'POST',
        headers: { 'content-type': 'application/json' },
        body: JSON.stringify({ port }),
        signal: AbortSignal.timeout(REQUEST_TIMEOUT_MS),
      });
      if (res.status === 200 || res.status === 409) return;
      if (res.status === 400 || res.status === 405) throw new Error(`register answered HTTP ${res.status}: ${await res.text()}`);
    } catch (err) {
      if (err instanceof Error && err.message.startsWith('register answered HTTP ')) throw err;
    }
    await sleep(retryDelay(attempt));
  }
}

/** Poll GET /done until it answers {"done":true}; never return before that. */
async function waitForDone(): Promise<void> {
  for (let attempt = 0; ; attempt += 1) {
    try {
      const res = await fetch(`${ENV_URL}/done`, { signal: AbortSignal.timeout(REQUEST_TIMEOUT_MS) });
      if (res.ok) {
        const body = (await res.json()) as { done?: unknown };
        if (body.done === true) return;
      }
    } catch {
      // The env is not answering yet, or the poll timed out: it is not done, so poll again.
    }
    await sleep(retryDelay(attempt));
  }
}

/** Bound the port, register it, then wait for the env: the whole life of the process. */
async function main(): Promise<void> {
  const server = createServer(createApp());
  await new Promise<void>((resolve, reject) => {
    server.once('error', reject);
    server.listen(0, () => resolve());
  });
  const address = server.address();
  if (address === null || typeof address === 'string') throw new Error('the server did not bind an ephemeral TCP port');
  process.stdout.write(`[entry] listening on port ${address.port}\n`);

  await register(address.port);
  process.stdout.write('[entry] registered; waiting for the env to say done\n');

  await waitForDone();
  server.close();
  process.stdout.write('[entry] done\n');
}

try {
  await main();
  process.exit(0);
} catch (err) {
  process.stderr.write(`[entry] ${err instanceof Error ? err.message : String(err)}\n`);
  process.exit(1);
}
