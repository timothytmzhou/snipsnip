import { readFileSync } from "node:fs";

import init, { TypeScriptAnalyzer } from "../dist/pkg/snipsnip_demo.js";

const wasm = readFileSync(
  new URL("../dist/pkg/snipsnip_demo_bg.wasm", import.meta.url),
);
await init({ module_or_path: wasm });

const defaultProgram = TypeScriptAnalyzer.defaultEgglogProgram();
if (
  !defaultProgram.includes("(datatype Expr") ||
  !defaultProgram.includes("(rewrite") ||
  !defaultProgram.includes("(birewrite")
) {
  throw new Error("the browser default does not expose its AST and typing rules");
}

const analyzer = new TypeScriptAnalyzer(defaultProgram);

const invalid = JSON.parse(
  analyzer.analyze("let answer: number = true;"),
);
if (invalid.realizability !== "unrealizable") {
  throw new Error(`expected an unrealizable TypeScript prefix: ${JSON.stringify(invalid)}`);
}
if (invalid.tokens.at(-2)?.realizability !== "unknown") {
  throw new Error("the open declaration should remain unknown until its semicolon");
}
if (invalid.tokens.at(-1)?.realizability !== "unrealizable") {
  throw new Error("the completed ill-typed declaration was not marked unrealizable");
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

const partial = JSON.parse(
  analyzer.analyze("let answer: numb"),
);
if (partial.pending?.lexeme !== "numb") {
  throw new Error(
    `the core lexer did not retain the incomplete suffix: ${JSON.stringify(partial)}`,
  );
}
if (partial.tokens.some((token) => token.lexeme === "numb")) {
  throw new Error("an incomplete suffix reached the parser token trace");
}

const withoutNumberTyping = defaultProgram.replace(
  "(birewrite (NumberLiteral) (NumberExpression))",
  "",
);
analyzer.setProgram(withoutNumberTyping);
const untyped = JSON.parse(
  analyzer.analyze("let answer: number = 42;"),
);
if (untyped.realizability !== "unknown") {
  throw new Error(
    `deleting the number-literal typing rule should remove the proof: ${JSON.stringify(untyped)}`,
  );
}

analyzer.free();
console.log("WASM smoke test passed: typing rules control the three-way result.");
