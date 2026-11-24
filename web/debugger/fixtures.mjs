// Usage: node fixtures.mjs [hevm]  -- rewrites test/fixtures from a running hevm debugger. Needs hevm and an
// SMT solver on PATH, e.g. in hevm's nix shell. The progress fixtures are kept: a run's progress is hard to catch.
import { spawn } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const hevm = process.argv[2] ?? "hevm";
const dir = path.join(path.dirname(fileURLToPath(import.meta.url)), "test", "fixtures");
// a loop writing memory, run concretely; a branch on calldata, run symbolically
const loop = "60005b8080526001018060201160025700";
const branch = "600035600514600a57005b00";

// durations and thread ids would change on every run
function withoutNoise(v) {
  if (Array.isArray(v)) return v.map(withoutNoise);
  if (v === null || typeof v !== "object") return v;
  return Object.fromEntries(
    Object.entries(v).map(([k, x]) => [k, /secs$/i.test(k) && typeof x === "number" ? 0 : k === "thread" ? "ThreadId 0" : withoutNoise(x)]),
  );
}

async function session(args, script) {
  const proc = spawn(hevm, [...args, "--interactive", "--port", "0"], { stdio: ["ignore", "pipe", "inherit"] });
  const port = await new Promise((resolve, reject) => {
    let out = "";
    proc.stdout.on("data", (d) => {
      out += d;
      const m = /http:\/\/127\.0\.0\.1:(\d+)/.exec(out);
      if (m) resolve(m[1]);
    });
    proc.on("exit", (code) => reject(new Error(`${hevm} exited with ${code} before serving`)));
  });
  const call = async (method, p, body) => {
    const r = await fetch(`http://127.0.0.1:${port}${p}`, { method, body });
    if (!r.ok) throw new Error(`${method} ${p}: ${r.status} ${await r.text()}`);
    return r.json();
  };
  const save = (name, v) => fs.writeFileSync(path.join(dir, `${name}.json`), JSON.stringify(withoutNoise(v), null, 4) + "\n");
  try {
    await script(call, save);
  } finally {
    await call("POST", "/quit").catch(() => {});
    proc.kill();
  }
}

await session(["exec", "--code", loop], async (call, save) => {
  await call("POST", "/command", "step 5");
  save("state-concrete", await call("GET", "/state"));
  save("stats", await call("GET", "/stats"));
  save("help", await call("GET", "/help"));
});
await session(["symbolic", "--code", branch], async (call, save) => {
  save("state-branch", await call("POST", "/command", "continue"));
  await call("POST", "/command", "break op STOP");
  save("state-breakpoint", await call("POST", "/command", "branch true"));
  await call("POST", "/command", "delete all");
  save("state-halted", await call("POST", "/command", "continue"));
  save("trace", await call("GET", "/trace"));
});
console.log(`rewrote the fixtures in ${dir}`);
