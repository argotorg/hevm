import { defineConfig } from "vitest/config";

// HEVM_DEBUGGER=http://127.0.0.1:7317 npm run dev: debugger/ then talks to that `hevm --interactive`
const hevm = process.env.HEVM_DEBUGGER;
const apiPaths = ["/state", "/command", "/stats", "/progress", "/help", "/trace", "/quit"];

export default defineConfig({
  base: "./",
  worker: { format: "es" },
  build: {
    rollupOptions: {
      input: { main: "index.html", debugger: "debugger/index.html" },
    },
  },
  server: hevm ? { proxy: Object.fromEntries(apiPaths.map((p) => [p, hevm])) } : {},
  resolve: {
    // the debugger's tests are written for node:test, whose describe and test vitest has too
    alias: { "node:test": "vitest" },
  },
  test: {
    testTimeout: 600_000,
  },
});
