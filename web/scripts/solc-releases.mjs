// Writes src/solcReleases.ts from solc's list of releases. Usage: node scripts/solc-releases.mjs [list.json]
import { readFileSync, writeFileSync } from "node:fs";

const url = "https://binaries.soliditylang.org/bin/list.json";
const list = process.argv[2] ? JSON.parse(readFileSync(process.argv[2], "utf8")) : await (await fetch(url)).json();
const releases = list.builds
  .filter((b) => !b.prerelease && list.releases[b.version] === b.path)
  .map((b) => b.longVersion)
  .filter((v) => { const [, minor, patch] = v.split(/[.+]/).map(Number); return minor > 4 || patch >= 11; })
  .reverse();
writeFileSync(new URL("../src/solcReleases.ts", import.meta.url), `// Made by scripts/solc-releases.mjs: solc's releases with standard JSON, newest first
export const solcReleases: string[] = ${JSON.stringify(releases, null, 2)};
`);
console.log(`${releases.length} releases, ${releases[0]} to ${releases.at(-1)}`);
