// Loads the built site (npm run build) in headless Chromium and runs examples through the UI.
import { existsSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { chromium, type Browser, type Page } from "playwright-core";
import { preview, type PreviewServer } from "vite";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { examples } from "../src/examples";

const root = fileURLToPath(new URL("..", import.meta.url));
const chrome = process.env.CHROME ?? "/usr/bin/chromium";
const ready = existsSync(`${root}/dist/hevm.wasm`) && existsSync(chrome);

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

  async function runExample(name: string) {
    await page.selectOption("#example", String(examples.findIndex((e) => e.name === name)));
    await page.click("#run");
    await page.waitForFunction(() => !(document.getElementById("run") as HTMLButtonElement).disabled);
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
