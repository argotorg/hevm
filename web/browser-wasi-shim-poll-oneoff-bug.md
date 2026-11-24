# browser_wasi_shim: `poll_oneoff` never writes the number of events

`poll_oneoff(in, out, nsubscriptions, nevents)` in `@bjorn3/browser_wasi_shim` 0.4.2
takes only the first three arguments. It writes the event to `out` but never stores
the count at `nevents`, so the caller reads whatever was in memory there.

wasi-libc's `poll`/`nanosleep` loop over that many events. With a stale large value they
read past the end of linear memory, and the module traps with
`RuntimeError: memory access out of bounds`. hevm (a GHC program, whose non-threaded RTS
sleeps with `poll_oneoff` on a timer) hit this a few seconds into some runs, the same
module ran fine on wasmtime and on Node's `node:wasi`.

The fix is to store 1 at `nevents` when the call succeeds, as `web/src/hevm.ts` does
around the shim's function:

```ts
const poll = wasi.wasiImport.poll_oneoff!;
wasi.wasiImport.poll_oneoff = (inPtr, outPtr, n, nevents) => {
  const ret = poll(inPtr, outPtr, n);
  if (ret === 0) new DataView(wasi.inst.exports.memory.buffer).setUint32(nevents, 1, true);
  return ret;
};
```
