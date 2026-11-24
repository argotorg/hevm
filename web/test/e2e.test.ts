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
      if (source !== undefined) {
        await page.click("#source .cm-content");
        await page.keyboard.press("ControlOrMeta+A");
        await page.keyboard.insertText(source);
      }
      await page.click("#prove");
      await idle("prove");
      return page.locator("#sol-results .card:not(.stats)");
    }

    it("shows a counterexample at its line in the source", async () => {
      const cards = await prove("Find x, prove a bound");
      await expect.poll(() => cards.count()).toBe(2);
      const failing = cards.filter({ hasText: "prove_linear" });
      expect(await failing.getAttribute("class")).toBe("card fail");
      expect(await failing.textContent()).toContain("prove_linear(31)");
      expect(await failing.textContent()).toContain("Panic(0x01): assertion failed");
      expect(await failing.locator(".excerpt .hit").textContent()).toBe("10            assert(x * 3 + 7 != 100);");
      expect(await failing.locator(".excerpt mark").textContent()).toBe("assert(x * 3 + 7 != 100)");
      // highlighted like the editor, the mark spanning the tokens
      expect(await failing.locator(".excerpt .tok-number").first().textContent()).toBe("3");
      expect(await failing.locator(".excerpt mark .tok-operator").count()).toBeGreaterThan(0);
      expect(await page.locator("#source .tok-keyword").first().textContent()).toBe("pragma");
      // and the editor shows the failing line
      expect(await page.locator("#source .cm-failing").textContent()).toBe("            assert(x * 3 + 7 != 100);");
      expect(await cards.filter({ hasText: "PASS" }).getAttribute("class")).toBe("card pass");
      expect(await page.textContent("#sol-status")).toMatch(/^1 passed, 1 failed/);
    });

    it("locates a failure inside a called contract", async () => {
      const cards = await prove("Failure in a called contract");
      expect(await cards.first().locator(".excerpt mark").textContent()).toBe("assert(total < 1000)");
    });

    it("shows progress while it runs, and statistics at the end", async () => {
      await page.click('.tabs [data-tab="sol"]');
      await page.selectOption("#sol-example", String(solExamples.findIndex((e) => e.name === "Sorting network")));
      await page.click("#prove");
      // a live update: the run takes seconds, the counters move before it ends
      await page.waitForFunction(() => {
        const bar = document.querySelector("#sol-progress .bar.busy");
        const dd = [...document.querySelectorAll("#sol-progress .counters dt")].find((d) => d.textContent === "Paths");
        return bar && Number(dd?.nextElementSibling?.textContent) > 0;
      });
      expect(await page.locator("#prove").isDisabled()).toBe(true);
      await idle("prove");
      expect(await page.textContent("#sol-progress .what")).toBe("Done");
      expect(await page.locator("#sol-progress .bar.busy").count()).toBe(0);
      expect(await page.locator("#sol-progress .counters").textContent()).toContain("Functions2 / 2");
    });

    it("has a row of statistics per function", async () => {
      const cards = await prove("Math library");
      expect(await cards.filter({ hasText: "FAIL" }).count()).toBe(2);
      const rows = page.locator("#sol-results .stats tr");
      expect(await rows.count()).toBe(7);
      expect(await page.locator("#sol-results .stats").textContent()).toMatch(/\d+ SMT queries: /);
      expect(await page.locator("#sol-progress .counters").textContent()).toContain("Functions6 / 6");
    });

    it("selects text in the page's colour, not CodeMirror's fixed purple", async () => {
      await page.click('.tabs [data-tab="sol"]');
      await page.click("#source .cm-line >> nth=7");
      await page.keyboard.press("Shift+ArrowDown");
      // drawn on the next frame
      const sel = await page.waitForSelector("#source .cm-selectionBackground");
      const bg = await sel.evaluate((e) => getComputedStyle(e).backgroundColor);
      const want = await page.evaluate(() => {
        const probe = document.createElement("div");
        probe.style.backgroundColor = "var(--selection)";
        document.body.append(probe);
        const c = getComputedStyle(probe).backgroundColor;
        probe.remove();
        return c;
      });
      expect(bg).toBe(want);
    });

    it("shows compile errors at their place", async () => {
      const cards = await prove("Find x, prove a bound", "pragma solidity ^0.8.0;\ncontract C { function f() public { x = 1; } }\n");
      expect(await cards.first().textContent()).toContain("Undeclared identifier");
      expect(await cards.first().locator(".excerpt mark").textContent()).toBe("x");
      expect(await page.textContent("#sol-status")).toMatch(/^Compilation failed/);
      expect(await page.locator("#sol-progress").isHidden()).toBe(true);
    });
  });

  describe("Layout", () => {
    async function boxes(width: number) {
      const p = await browser.newPage({ viewport: { width, height: 900 } });
      await p.goto(server.resolvedUrls!.local[0]!);
      const form = (await p.locator("#sol-form").boundingBox())!;
      const results = (await p.locator("#sol-results").boundingBox())!;
      const inside = await Promise.all(["#sol-example", "#source .cm-editor"].map(async (sel) => {
        const b = (await p.locator(sel).boundingBox())!;
        return b.x >= form.x && b.x + b.width <= form.x + form.width + 0.5;
      }));
      await p.close();
      return { form, results, inside };
    }

    it("puts the results beside the code when there is room", async () => {
      const { form, results, inside } = await boxes(1400);
      expect(inside).toEqual([true, true]);
      expect(results.x).toBeGreaterThanOrEqual(form.x + form.width);
      expect(results.y).toBeLessThan(form.y + form.height);
    });

    it("never scrolls sideways on a phone, however long the code lines", async () => {
      const p = await browser.newPage({ viewport: { width: 420, height: 900 } });
      await p.goto(server.resolvedUrls!.local[0]!);
      await p.click("#prove");
      await p.waitForFunction(() => !(document.getElementById("prove") as HTMLButtonElement).disabled);
      expect(await p.locator("#sol-results .excerpt").count()).toBeGreaterThan(0);
      const [scroll, width] = await p.evaluate(() => [document.documentElement.scrollWidth, window.innerWidth]);
      await p.close();
      expect(scroll).toBeLessThanOrEqual(width);
    });

    it("stacks them on a narrow screen", async () => {
      const { form, results, inside } = await boxes(600);
      expect(inside).toEqual([true, true]);
      expect(results.y).toBeGreaterThanOrEqual(form.y + form.height);
      expect(results.x).toBeLessThan(form.x + 1);
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
