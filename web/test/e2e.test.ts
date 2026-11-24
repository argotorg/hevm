// Loads the built site (npm run build) in headless Chromium and runs examples through the UI.
import { existsSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { chromium, type Browser, type Page } from "playwright-core";
import { preview, type PreviewServer } from "vite";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { examples } from "../src/examples";
import { solExamples } from "../src/solExamples";
import { eqExamples } from "../src/eqExamples";
import { encodeShare } from "../src/share";

const root = fileURLToPath(new URL("..", import.meta.url));
const chrome = process.env.CHROME ?? "/usr/bin/chromium";
const ready = ["hevm.wasm", "hevm-web.wasm", "hevm-web.js", "soljson.js"].every((f) => existsSync(`${root}/dist/${f}`)) && existsSync(chrome);

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
      // a live update: the run takes seconds, the counters move before it ends, and the bar
      // names the function being checked
      const label = await page.waitForFunction(() => {
        const bar = document.querySelector("#sol-progress .bar.busy");
        const dd = [...document.querySelectorAll("#sol-progress .counters dt")].find((d) => d.textContent === "Paths");
        const label = bar?.querySelector(".label")?.textContent ?? "";
        return Number(dd?.nextElementSibling?.textContent) > 0 && /^prove_\w+ · [12] of 2$/.test(label) && label;
      });
      expect(await label.jsonValue()).toMatch(/^prove_(sorted|permutation) /);
      expect(await page.locator("#prove").isDisabled()).toBe(true);
      await idle("prove");
      expect(await page.textContent("#sol-progress .label")).toBe("Done: 2 of 2 functions");
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

    it("draws the cursor in the accent colour, visible in dark mode too", async () => {
      await page.emulateMedia({ colorScheme: "dark" });
      await page.click('.tabs [data-tab="sol"]');
      await page.click("#source .cm-line >> nth=3");
      const cursor = await page.waitForSelector("#source .cm-cursor-primary");
      const [color, width] = await cursor.evaluate((e) => [getComputedStyle(e).borderLeftColor, getComputedStyle(e).borderLeftWidth]);
      const want = await page.evaluate(() => {
        const probe = document.createElement("div");
        probe.style.color = "var(--accent)";
        document.body.append(probe);
        const c = getComputedStyle(probe).color;
        probe.remove();
        return c;
      });
      await page.emulateMedia({ colorScheme: null });
      expect(color).toBe(want);
      expect(width).toBe("2px");
    });

    it("opens on the Parity wallet, with its story", async () => {
      const p = await browser.newPage();
      await p.goto(server.resolvedUrls!.local[0]!);
      expect(await p.locator("#sol-example option:checked").textContent()).toBe("Re-initializable wallet (Parity, 2017)");
      expect(await p.textContent("#sol-story")).toContain("initWallet");
      expect(await p.textContent("#source .cm-content")).toContain("function initWallet()");
      await p.close();
    });

    it("groups the examples, and tells the story of a real bug", async () => {
      await page.click('.tabs [data-tab="sol"]');
      expect(await page.locator("#sol-example optgroup").evaluateAll((gs) => gs.map((g) => (g as HTMLOptGroupElement).label)))
        .toEqual(["Invariants", "Real bug patterns"]);
      await page.selectOption("#sol-example", "0");
      expect(await page.locator("#sol-story").isHidden()).toBe(true);
      await page.selectOption("#sol-example", String(solExamples.findIndex((e) => e.name.startsWith("Batch transfer overflow"))));
      expect(await page.textContent("#sol-story")).toContain("CVE-2018-10299");
      const cards = await prove("Batch transfer overflow (BeautyChain, 2018)");
      // the value of the real attack: 2^255
      expect(await cards.first().locator("dd").first().textContent()).toMatch(new RegExp(`,0x8${"0".repeat(63)}\\)$`));
    });

    it("shows the calls that break an invariant", async () => {
      const cards = await prove("Escrow state machine");
      const card = cards.filter({ hasText: "invariant_one_outcome" });
      expect(await card.locator("ol.calls li").allTextContents()).toEqual([
        "Escrow.release() from 0x0000000000000000000000000000000000000B0b",
        "Escrow.refund() from 0x00000000000000000000000000000000005E11e7",
      ]);
      expect(await card.getByRole("button").count()).toBe(0);
      const row = page.locator("#sol-results .stats tr").filter({ hasText: "invariant_one_outcome" });
      expect(await row.locator("td").last().textContent()).toBe("1");
    });

    it("shows compile errors at their place", async () => {
      const cards = await prove("Find x, prove a bound", "pragma solidity ^0.8.0;\ncontract C { function f() public { x = 1; } }\n");
      expect(await cards.first().textContent()).toContain("Undeclared identifier");
      expect(await cards.first().locator(".excerpt mark").textContent()).toBe("x");
      expect(await page.textContent("#sol-status")).toMatch(/^Compilation failed/);
      expect(await page.locator("#sol-progress").isHidden()).toBe(true);
    });
  });

  describe("Debugger", () => {
    const debuggerFrame = () => page.frameLocator("#debugger");

    async function proveFirstExample() {
      await page.click('.tabs [data-tab="sol"]');
      await page.selectOption("#sol-example", String(solExamples.findIndex((e) => e.name === "Find x, prove a bound")));
      await page.click("#prove");
      await idle("prove");
      return page.locator("#sol-results .card:not(.stats)").filter({ hasText: "prove_linear" });
    }

    it("has no tab until there is something to debug", async () => {
      const p = await browser.newPage();
      await p.goto(server.resolvedUrls!.local[0]!);
      expect(await p.locator('.tabs [data-tab="debug"]').isHidden()).toBe(true);
      await p.close();
    });

    it("replays a counterexample to its failure", async () => {
      const card = await proveFirstExample();
      await card.getByRole("button", { name: "Replay in debugger" }).click();
      expect(await page.locator('.tabs [data-tab="debug"]').isVisible()).toBe(true);
      expect(await page.locator("#debugger").isVisible()).toBe(true);
      expect(await page.textContent("#debug-caption")).toBe(
        "Replaying prove_linear(31): step through it, or press Continue to run to where it fails.");
      const frame = debuggerFrame();
      await frame.locator("#status .step").waitFor();
      await frame.getByRole("button", { name: /^Continue/ }).click();
      // Panic(0x01): the assertion
      await expect.poll(() => frame.locator("#result").textContent(), { timeout: 60_000 }).toMatch(/^revert, returned 0x4e487b7100*1$/);
      expect(await frame.locator("#status").textContent()).toContain("halted");
    });

    it("debugs a function symbolically", async () => {
      const card = await proveFirstExample();
      await card.getByRole("button", { name: "Debug symbolically" }).click();
      expect(await page.textContent("#debug-caption")).toMatch(/^Debugging prove_linear for all inputs at once/);
      const frame = debuggerFrame();
      await frame.locator("#status .step").waitFor();
      expect(await frame.locator("#status").textContent()).toContain("symbolic");
    });

    it("sends a counterexample to the Bytecode tab", async () => {
      const card = await proveFirstExample();
      await card.getByRole("button", { name: "Open in Bytecode tab" }).click();
      expect(await page.inputValue("#calldata")).toBe("0x82d4ea10" + "1f".padStart(64, "0"));
      expect((await page.inputValue("#code")).length).toBeGreaterThan(100);
      await page.click("#run");
      await idle("run");
      expect(await page.getAttribute("#outcome", "class")).toBe("outcome revert");
      expect(await page.textContent("#outcome")).toContain("4e487b71");
    });
  });

  describe("Equivalence", () => {
    async function check(name: string) {
      await page.click('.tabs [data-tab="eq"]');
      await page.selectOption("#eq-example", String(eqExamples.findIndex((e) => e.name === name)));
      await page.click("#eq-check");
      await idle("eq-check");
      return page.locator("#eq-results .card");
    }

    it("proves two contracts equivalent", async () => {
      const card = await check("Branch-free min and max");
      expect(await card.locator(".badge").textContent()).toBe("EQUIVALENT");
      expect(await page.textContent("#eq-status")).toMatch(/^Equivalent — /);
    });

    it("shows an input where they differ, and what each does", async () => {
      const card = await check("Forgot the zero case");
      expect(await card.locator(".badge").textContent()).toBe("DIFFERENT");
      expect(await card.locator("dd").first().textContent()).toBe("isPowerOfTwo(0)");
      expect(await card.textContent()).toContain("Carefulreturns false");
      expect(await card.textContent()).toContain("Forgetfulreturns true");
    });

    it("runs a program on the input in the Bytecode tab", async () => {
      const card = await check("Forgot the zero case");
      await card.getByRole("button", { name: "Run Forgetful in Bytecode tab" }).click();
      expect(await page.getAttribute("body", "data-tab")).toBe("bytecode");
      await page.click("#run");
      await idle("run");
      expect(await page.textContent("#outcome code")).toBe("0x" + "1".padStart(64, "0"));
    });

    it("offers the contracts of the source, and one for the compiler comparisons", async () => {
      await page.click('.tabs [data-tab="eq"]');
      await page.selectOption("#eq-example", String(eqExamples.findIndex((e) => e.name === "Legacy codegen vs via-IR")));
      expect(await page.locator("#eq-b-field").isHidden()).toBe(true);
      await page.selectOption("#eq-mode", "contracts");
      expect(await page.locator("#eq-b-field").isVisible()).toBe(true);
      await page.click("#eq-source .cm-content");
      await page.keyboard.press("Control+End");
      await page.keyboard.type("\ncontract Other {}\n");
      expect(await page.locator("#eq-b option").allTextContents()).toEqual(["Packing", "Other"]);
      expect(await page.inputValue("#eq-b")).toBe("Other");
    });
  });

  describe("Links", () => {
    async function open(hash: string) {
      const p = await browser.newPage();
      await p.goto(`${server.resolvedUrls!.local[0]!}#${hash}`);
      return p;
    }

    it("open an example and prove it", async () => {
      const p = await open("tab=sol&example=Unsafe+downcast");
      await p.waitForSelector("#sol-results .card.fail");
      expect(await p.inputValue("#sol-example")).toBe(String(solExamples.findIndex((e) => e.name === "Unsafe downcast")));
      expect(await p.textContent("#sol-story")).toContain("SafeCast");
      await p.close();
    });

    it("carry edited code to another page, which proves it", async () => {
      await page.click('.tabs [data-tab="sol"]');
      await page.selectOption("#sol-example", "0");
      await page.click("#source .cm-content");
      await page.keyboard.press("ControlOrMeta+A");
      const source = "pragma solidity ^0.8.0;\nimport {Test} from \"hevm/Test.sol\";\ncontract T is Test {\n  function prove_small(uint8 x) public pure { assert(x != 7); }\n}\n";
      await page.keyboard.insertText(source);
      await page.click("#sol-share");
      await expect.poll(() => page.textContent("#sol-status")).toMatch(/^(Link copied|The link is in the address bar)$/);
      const hash = new URL(page.url()).hash.slice(1);
      expect(hash).toMatch(/^tab=sol&s=/);
      const p = await open(hash);
      await p.waitForSelector("#sol-results .card.fail");
      expect(await p.locator("#sol-results .card.fail dd").first().textContent()).toBe("prove_small(7)");
      expect(await p.inputValue("#sol-example")).toBe("");
      await p.close();
    });

    it("open the Equivalence tab with its settings, and check", async () => {
      await page.click('.tabs [data-tab="eq"]');
      await page.selectOption("#eq-example", String(eqExamples.findIndex((e) => e.name === "Forgot the zero case")));
      await page.click("#eq-share");
      await expect.poll(() => new URL(page.url()).hash).toMatch(/^#tab=eq&example=/);
      const p = await open(new URL(page.url()).hash.slice(1));
      await p.waitForSelector("#eq-results .card.fail");
      expect(await p.getAttribute("body", "data-tab")).toBe("eq");
      expect(await p.locator("#eq-results dd").first().textContent()).toBe("isPowerOfTwo(0)");
      await p.close();
    });

    it("open the Bytecode tab, and run it", async () => {
      const p = await open(`tab=bytecode&s=${(await encodeShare({ tab: "bytecode", request: { mode: "exec", code: "0x602a60005260206000f3", calldata: "", sig: "" } })).split("&s=")[1]}`);
      await p.waitForSelector("#outcome.return");
      expect(await p.textContent("#outcome code")).toBe("0x" + "2a".padStart(64, "0"));
      await p.close();
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

    it("has the tabs in order, the Debugger last", async () => {
      expect(await page.locator(".tabs button").allTextContents()).toEqual(["Solidity", "Equivalence", "Bytecode", "Debugger"]);
    });

    it("fits all the tabs on a phone", async () => {
      const p = await browser.newPage({ viewport: { width: 360, height: 700 } });
      await p.goto(server.resolvedUrls!.local[0]!);
      const [scroll, width] = await p.evaluate(() => {
        const tabs = document.querySelector(".tabs")!;
        return [tabs.scrollWidth, tabs.clientWidth];
      });
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
