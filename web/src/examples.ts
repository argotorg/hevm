import type { Request } from "./hevm";

export interface Example {
  name: string;
  request: Request;
}

export const examples: Example[] = [
  {
    name: "Find the input that fails an assertion",
    // fails (INVALID) iff the first calldata word is 42
    request: { mode: "symbolic", code: "0x600035602a14600a57005bfe" },
  },
  {
    name: "Solve 3x + 7 = 100 (mod 2^256)",
    // fails iff 3 * calldata[0:32] + 7 == 100
    request: { mode: "symbolic", code: "0x600035600302600701606414601057005bfe" },
  },
  {
    name: "Prove no input fails",
    // compares calldata to 42 and stops either way
    request: { mode: "symbolic", code: "0x600035602a1400" },
  },
  {
    name: "Keccak of 32 zero bytes",
    request: { mode: "exec", code: "0x602060002060005260206000f3" },
  },
  {
    name: "ecrecover precompile",
    // copies calldata to memory, calls 0x01, returns the recovered address
    request: {
      mode: "exec",
      code: "0x608060006000376020600060806000600162fffffffa5060206000f3",
      calldata:
        "0x513954cf30af6638cb8f626bd3f8c39183c26784ce826084d9d267868a18fb31" +
        "000000000000000000000000000000000000000000000000000000000000001c" +
        "c84e55cee2032ea541a32bf6749e10c8b9344c92061724c4e751600f886f4732" +
        "1542b6457e91098682138856165381453b3d0acae2470286fd8c8a09914b1b5d",
    },
  },
  {
    name: "Revert",
    request: { mode: "exec", code: "0x60006000fd" },
  },
];
