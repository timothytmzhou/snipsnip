import { readFileSync } from "node:fs";

import init, { TypeScriptAnalyzer } from "../dist/pkg/snipsnip_demo.js";

const wasm = readFileSync(
  new URL("../dist/pkg/snipsnip_demo_bg.wasm", import.meta.url),
);
await init({ module_or_path: wasm });

const analyzer = new TypeScriptAnalyzer(
  TypeScriptAnalyzer.defaultEgglogProgram(),
);

const invalid = JSON.parse(
  analyzer.analyze("let answer: number = true;"),
);
if (invalid.realizability !== "unrealizable") {
  throw new Error(`expected an unrealizable TypeScript prefix: ${JSON.stringify(invalid)}`);
}
if (invalid.tokens.at(-2)?.realizability !== "unrealizable") {
  throw new Error("the mismatched `true` token was not marked unrealizable");
}

const valid = JSON.parse(
  analyzer.analyze("let answer: number = 42;"),
);
if (valid.realizability !== "realizable") {
  throw new Error(`expected a realizable TypeScript prefix: ${JSON.stringify(valid)}`);
}
if (!valid.tokens.every((token) => token.elapsedMs >= 0)) {
  throw new Error("the token trace did not include timings");
}

analyzer.free();
console.log("WASM smoke test passed: invalid and valid TypeScript traces agree.");
