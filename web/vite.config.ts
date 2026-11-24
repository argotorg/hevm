import { defineConfig } from "vitest/config";

export default defineConfig({
  base: "./",
  worker: { format: "es" },
  test: {
    testTimeout: 600_000,
  },
});
