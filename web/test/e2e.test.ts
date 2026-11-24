// Loads the built site (npm run build) in headless Chromium and runs examples through the UI.
import { existsSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { chromium, type Browser, type Page } from "playwright-core";
import { preview, type PreviewServer } from "vite";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { examples } from "../src/examples";
import { solExamples } from "../src/solExamples";

const root = fileURLToPath(new URL("..", import.meta.url));
const chrome = process.env.CHROME ?? "/usr/bin/chromium";
const ready = existsSync(`${root}/dist/hevm.wasm`) && existsSync(`${root}/dist/soljson.js`) && existsSync(chrome);

describe.skipIf(!ready)("website in Chromium", () => {
  let server: PreviewServer;
  let browser: Browser;
  let page: Page;

  beforeAll(async () => {
    server = await preview({ root, preview: { port: 0, host: "127.0.0.1" }, logLevel: "silent" });
    browser = await chromium.launch({ executablePath: chrome, args: ["--no-sandbox"] });
    page = await browser.newPage();
    await page.goto(server.resolvedUrls!.local[0]!);
  });

  afterAll(async () => {
    await browser?.close();
    await server?.close();
  });

  const idle = (button: string) =>
    page.waitForFunction((b) => !(document.getElementById(b) as HTMLButtonElement).disabled, button);

  describe("Solidity", () => {
    async function prove(name: string, source?: string) {
      await page.click('.tabs [data-tab="sol"]');
      await page.selectOption("#sol-example", String(solExamples.findIndex((e) => e.name === name)));
      if (source !== undefined) await page.fill("#source", source);
      await page.click("#prove");
      await idle("prove");
      return page.locator("#sol-results .card");
    }

    it("shows a counterexample at its line in the source", async () => {
      const cards = await prove("Assertions");
      await expect.poll(() => cards.count()).toBe(2);
      const failing = cards.filter({ hasText: "prove_linear" });
      expect(await failing.getAttribute("class")).toBe("card fail");
      expect(await failing.textContent()).toContain("prove_linear(31)");
      expect(await failing.textContent()).toContain("Panic(0x01): assertion failed");
      expect(await failing.locator(".excerpt .hit").textContent()).toBe("10            assert(x * 3 + 7 != 100);");
      expect(await failing.locator(".excerpt mark").textContent()).toBe("assert(x * 3 + 7 != 100)");
      expect(await cards.filter({ hasText: "prove_fits" }).getAttribute("class")).toBe("card pass");
      expect(await page.textContent("#sol-status")).toMatch(/^1 passed, 1 failed/);
    });

    it("locates a failure inside a called contract", async () => {
      const cards = await prove("Failure in a called contract");
      expect(await cards.first().locator(".excerpt mark").textContent()).toBe("assert(total < 1000)");
    });

    it("shows compile errors at their place", async () => {
      const cards = await prove("Assertions", "pragma solidity ^0.8.0;\ncontract C { function f() public { x = 1; } }\n");
      expect(await cards.first().textContent()).toContain("Undeclared identifier");
      expect(await cards.first().locator(".excerpt mark").textContent()).toBe("x");
      expect(await page.textContent("#sol-status")).toMatch(/^Compilation failed/);
    });
  });

  describe("Bytecode", () => {
    async function runExample(name: string) {
      await page.click('.tabs [data-tab="bytecode"]');
      await page.selectOption("#example", String(examples.findIndex((e) => e.name === name)));
      await page.click("#run");
      await idle("run");
      return {
        kind: await page.getAttribute("#outcome", "class"),
        text: await page.textContent("#outcome"),
      };
    }

    it("finds a counterexample with bitwuzla", async () => {
      const res = await runExample("Find the input that fails an assertion");
      expect(res.kind).toBe("outcome counterexamples");
      expect(res.text).toContain("0x000000000000000000000000000000000000000000000000000000000000002a");
    });

    it("proves a contract", async () => {
      expect((await runExample("Prove no input fails")).kind).toBe("outcome safe");
    });

    it("runs concrete code", async () => {
      const res = await runExample("ecrecover precompile");
      expect(res.kind).toBe("outcome return");
      expect(res.text).toContain("2d5e56d45c63150d937f2182538a0f18510cb11f");
    });

    it("shows bad input as an error without running hevm", async () => {
      await page.fill("#code", "0x6");
      await page.click("#run");
      expect(await page.getAttribute("#outcome", "class")).toBe("outcome error");
      expect(await page.textContent("#outcome")).toContain("code must be hex bytes");
    });
  });
});
