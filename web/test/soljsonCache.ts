// Old soljson builds for the tests, from web/.cache/soljson; download them there with
// curl -o web/.cache/soljson/soljson-v<version>.js https://binaries.soliditylang.org/bin/soljson-v<version>.js
import { existsSync, readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

const dir = fileURLToPath(new URL("../.cache/soljson/", import.meta.url));

export const soljsonPath = (version: string) => `${dir}soljson-v${version}.js`;
export const hasSoljson = (version: string) => existsSync(soljsonPath(version));
export const soljsonText = (version: string) => readFileSync(soljsonPath(version), "utf8");
