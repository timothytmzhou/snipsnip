/*
 * Message protocol
 * ----------------
 * Main thread -> worker:
 *   { type: "analyze", id, program, source }
 *
 * Worker -> main thread:
 *   { type: "ready", defaultProgram }
 *   { type: "result", id, result }
 *   { type: "error", id, error: { message, stack? } }
 *   { type: "engine-error", error: { message, stack? } }
 *
 * Expected wasm-bindgen API in ./pkg/snipsnip_demo.js:
 *
 *   default async function init(): Promise<void>
 *
 *   class TypeScriptAnalyzer {
 *     constructor(program: string)
 *     setProgram(program: string): void
 *     reset(): void
 *     analyze(source: string): string
 *     free?(): void
 *   }
 *
 * `analyze` returns JSON with this shape. `start` and `end` are UTF-16 source
 * offsets so the browser can select a prefix without translating byte offsets.
 *
 *   {
 *     realizability: "realizable" | "unrealizable" | "unknown",
 *     tokens: Array<{
 *       terminal: string,
 *       lexeme: string,
 *       start: number,
 *       end: number,
 *       realizability: "realizable" | "unrealizable" | "unknown",
 *       elapsedMs: number
 *     }>,
 *     totalMs: number,
 *     incremental: boolean
 *   }
 *
 * The analyzer owns the incremental parser/e-graph state. Calls may contain an
 * append, deletion, or arbitrary edit; `analyze` is responsible for reusing the
 * current prefix when possible and resetting when it is not. The worker caches
 * one analyzer and updates it only when the Egglog program changes.
 */

let AnalyzerClass;
let analyzer = null;
let configuredProgram = null;

const ready = initialize();
let requestQueue = Promise.resolve();

self.addEventListener("message", (event) => {
  requestQueue = requestQueue
    .then(() => handleMessage(event.data))
    .catch((error) => {
      // Keep the queue usable if an unexpected exception escapes handleMessage.
      self.postMessage({ type: "engine-error", error: serializeError(error) });
    });
});

async function initialize() {
  try {
    const bindings = await import("./pkg/snipsnip_demo.js");
    await bindings.default();

    if (typeof bindings.TypeScriptAnalyzer !== "function") {
      throw new TypeError("The WebAssembly module does not export TypeScriptAnalyzer.");
    }

    AnalyzerClass = bindings.TypeScriptAnalyzer;
    self.postMessage({
      type: "ready",
      defaultProgram: AnalyzerClass.defaultEgglogProgram(),
    });
  } catch (error) {
    self.postMessage({ type: "engine-error", error: serializeError(error) });
    throw error;
  }
}

async function handleMessage(message) {
  if (!message || message.type !== "analyze") return;

  const { id, program, source } = message;

  try {
    await ready;
    configureAnalyzer(String(program ?? ""));

    const startedAt = performance.now();
    const encoded = analyzer.analyze(String(source ?? ""));
    const workerMs = performance.now() - startedAt;
    const result = parseResult(encoded);

    self.postMessage({
      type: "result",
      id,
      result: { ...result, workerMs },
    });
  } catch (error) {
    // `setProgram` is atomic, and `analyze` resets itself after a non-extension,
    // so a bad edit does not force us to throw away the last valid setup.
    self.postMessage({ type: "error", id, error: serializeError(error) });
  }
}

function configureAnalyzer(program) {
  if (!analyzer) {
    analyzer = new AnalyzerClass(program);
    configuredProgram = program;
    return;
  }

  if (program !== configuredProgram) {
    analyzer.setProgram(program);
    configuredProgram = program;
  }
}

function parseResult(encoded) {
  const result = typeof encoded === "string" ? JSON.parse(encoded) : encoded;

  if (!result || typeof result !== "object" || Array.isArray(result)) {
    throw new TypeError("TypeScriptAnalyzer.analyze() returned an invalid result.");
  }

  if (!Array.isArray(result.tokens)) {
    throw new TypeError("Analyzer result is missing its token trace.");
  }

  return result;
}

function serializeError(error) {
  if (error instanceof Error) {
    return { message: error.message, stack: error.stack };
  }
  return { message: String(error) };
}
