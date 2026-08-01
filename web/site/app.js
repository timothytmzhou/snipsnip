const VALID_SAMPLE = "let answer: number = 42;";
const INVALID_SAMPLE = "let answer: number = true;";
const KEYWORDS = ["let", "number", "string", "boolean", "true", "false", "length"];
const INPUT_DEBOUNCE_MS = 300;

const programInput = document.querySelector("#egglog-program");
const sourceInput = document.querySelector("#source-input");
const resetProgramButton = document.querySelector("#reset-program");
const validSampleButton = document.querySelector("#sample-valid");
const invalidSampleButton = document.querySelector("#sample-invalid");
const statusBadge = document.querySelector("#overall-status");
const statusLabel = document.querySelector("#overall-status-label");
const totalTime = document.querySelector("#total-time");
const tokenStrip = document.querySelector("#token-strip");
const traceHint = document.querySelector("#trace-hint");
const errorPanel = document.querySelector("#error-panel");
const errorMessage = document.querySelector("#error-message");
const dismissErrorButton = document.querySelector("#dismiss-error");

programInput.value = "";
sourceInput.value = INVALID_SAMPLE;

let worker = null;
let workerReady = false;
let engineFailed = false;
let defaultProgram = "";
let debounceTimer = null;
let editVersion = 0;
let nextRequestId = 1;
let latestRequestId = 0;
const requests = new Map();

startWorker();

programInput.addEventListener("input", queueAnalysis);
sourceInput.addEventListener("input", queueAnalysis);

for (const input of [programInput, sourceInput]) {
  input.addEventListener("keydown", (event) => {
    if (event.key === "Enter" && (event.metaKey || event.ctrlKey)) {
      event.preventDefault();
      queueAnalysis({ immediate: true });
    }
  });
}

resetProgramButton.addEventListener("click", () => {
  programInput.value = defaultProgram;
  queueAnalysis({ immediate: true });
  programInput.focus();
});

validSampleButton.addEventListener("click", () => loadSample(VALID_SAMPLE));
invalidSampleButton.addEventListener("click", () => loadSample(INVALID_SAMPLE));

dismissErrorButton.addEventListener("click", () => {
  errorPanel.hidden = true;
});

tokenStrip.addEventListener("click", (event) => {
  const token = event.target.closest(".token");
  if (!token) return;

  const end = token.dataset.end === undefined ? Number.NaN : Number(token.dataset.end);
  if (Number.isFinite(end)) {
    sourceInput.value = sourceInput.value.slice(0, end);
    sourceInput.focus();
    sourceInput.setSelectionRange(sourceInput.value.length, sourceInput.value.length);
    queueAnalysis({ immediate: true });
  } else {
    sourceInput.focus();
    sourceInput.setSelectionRange(sourceInput.value.length, sourceInput.value.length);
  }
});

function startWorker() {
  if (!("Worker" in window)) {
    engineFailed = true;
    showError("This browser does not support Web Workers, which this demo requires.");
    setStatus("unknown", "Unknown · worker unavailable");
    return;
  }

  worker = new Worker(new URL("./analyzer-worker.js", import.meta.url), { type: "module" });
  worker.addEventListener("message", handleWorkerMessage);
  worker.addEventListener("error", (event) => {
    engineFailed = true;
    showError(event.message || "The analyzer worker stopped unexpectedly.");
    setStatus("unknown", "Unknown · engine error");
    setBusy(false);
  });
}

function handleWorkerMessage(event) {
  const message = event.data ?? {};

  if (message.type === "ready") {
    defaultProgram = String(message.defaultProgram ?? "");
    if (programInput.value === "") programInput.value = defaultProgram;
    workerReady = true;
    engineFailed = false;
    queueAnalysis({ immediate: true });
    return;
  }

  if (message.type === "engine-error") {
    engineFailed = true;
    showError(formatError(message.error));
    setStatus("unknown", "Unknown · engine unavailable");
    setBusy(false);
    return;
  }

  const request = requests.get(message.id);
  requests.delete(message.id);

  // A response is stale as soon as either editor changes, even during the
  // debounce window before its replacement request is posted.
  if (!request || request.version !== editVersion || message.id !== latestRequestId) {
    return;
  }

  setBusy(false);

  if (message.type === "error") {
    showError(formatError(message.error));
    setStatus("unknown", "Unknown · analysis error");
    totalTime.textContent = "—";
    return;
  }

  if (message.type === "result") {
    hideError();
    renderResult(message.result, request);
  }
}

function queueAnalysis(options = {}) {
  editVersion += 1;
  const version = editVersion;
  clearTimeout(debounceTimer);

  if (engineFailed) return;

  setBusy(true);
  debounceTimer = window.setTimeout(
    () => submitAnalysis(version),
    options.immediate ? 0 : INPUT_DEBOUNCE_MS,
  );
}

function submitAnalysis(version) {
  if (version !== editVersion || engineFailed) return;

  if (!workerReady) {
    setStatus("loading", "Loading engine");
    return;
  }

  const source = sourceInput.value;
  const pending = trailingPendingLexeme(source);
  const analyzedSource = pending ? source.slice(0, pending.start) : source;
  const id = nextRequestId++;

  latestRequestId = id;
  requests.set(id, { version, source, analyzedSource, pending });
  pruneOldRequests(id);

  worker.postMessage({
    type: "analyze",
    id,
    program: programInput.value,
    source: analyzedSource,
  });
}

function pruneOldRequests(latestId) {
  for (const id of requests.keys()) {
    if (id < latestId - 8) requests.delete(id);
  }
}

function loadSample(source) {
  sourceInput.value = source;
  sourceInput.focus();
  sourceInput.setSelectionRange(source.length, source.length);
  queueAnalysis({ immediate: true });
}

function renderResult(rawResult, request) {
  const result = rawResult && typeof rawResult === "object" ? rawResult : {};
  const tokens = Array.isArray(result.tokens) ? result.tokens : [];
  const fragment = document.createDocumentFragment();

  for (const token of tokens) {
    fragment.append(createToken(token, request.source));
  }

  if (request.pending) {
    fragment.append(createPendingToken(request.pending));
  }

  if (tokens.length === 0 && !request.pending) {
    const empty = document.createElement("div");
    empty.className = "token-empty";
    empty.textContent = "No lexemes yet · showing the result for ε";
    fragment.append(empty);
  }

  tokenStrip.replaceChildren(fragment);

  const elapsed = finiteNumber(result.totalMs) ?? finiteNumber(result.workerMs);
  totalTime.textContent = formatDuration(elapsed);

  if (request.pending) {
    setStatus("unknown", "Unknown · incomplete lexeme");
    traceHint.textContent = `${request.pending.label} is held outside the parser until it is complete.`;
  } else {
    const status = normalizeRealizability(result.realizability);
    setStatus(status, statusLabelFor(status));
    traceHint.textContent = result.incremental
      ? "Incremental prefix reuse · Select a token to return to that exact prefix."
      : "Select a token to put the editor at that exact prefix.";
  }

  tokenStrip.setAttribute("aria-busy", "false");
}

function createToken(rawToken, source) {
  const token = rawToken && typeof rawToken === "object" ? rawToken : {};
  const status = normalizeRealizability(token.realizability);
  const lexeme = String(token.lexeme ?? "");
  const terminal = String(token.terminal ?? "token");
  const elapsed = finiteNumber(token.elapsedMs);
  const end = finiteNumber(token.end);
  const button = document.createElement("button");

  button.type = "button";
  button.className = `token token-${status}`;
  if (end !== null) {
    button.dataset.end = String(Math.min(end, source.length));
  }
  button.title = `${terminal} · ${statusLabelFor(status)} after this prefix`;
  button.setAttribute(
    "aria-label",
    `${visibleLexeme(lexeme)}, ${terminal}, ${statusLabelFor(status)}, ${formatDuration(elapsed)}`,
  );

  const lexemeElement = document.createElement("span");
  lexemeElement.className = "token-lexeme";
  lexemeElement.textContent = visibleLexeme(lexeme);

  const meta = document.createElement("span");
  meta.className = "token-meta";
  meta.textContent = formatDuration(elapsed);

  button.append(lexemeElement, meta);
  return button;
}

function createPendingToken(pending) {
  const button = document.createElement("button");
  button.type = "button";
  button.className = "token token-pending";
  button.title = pending.label;
  button.setAttribute("aria-label", `${visibleLexeme(pending.lexeme)}, ${pending.label}`);

  const lexeme = document.createElement("span");
  lexeme.className = "token-lexeme";
  lexeme.textContent = visibleLexeme(pending.lexeme);

  const meta = document.createElement("span");
  meta.className = "token-meta";
  meta.textContent = "pending";

  button.append(lexeme, meta);
  return button;
}

function trailingPendingLexeme(source) {
  const openString = findOpenString(source);
  if (openString !== null) {
    return {
      start: openString,
      end: source.length,
      lexeme: source.slice(openString),
      label: "Unterminated string literal",
    };
  }

  const identifier = source.match(/[A-Za-z_][A-Za-z0-9_]*$/u);
  if (!identifier) return null;

  const lexeme = identifier[0];
  const start = source.length - lexeme.length;
  const keyword = KEYWORDS.find(
    (candidate) =>
      candidate !== lexeme &&
      candidate.startsWith(lexeme) &&
      keywordContextMatches(source, start, candidate),
  );
  if (!keyword) return null;

  return {
    start,
    end: source.length,
    lexeme,
    label: `Incomplete keyword · expected “${keyword}”`,
  };
}

function keywordContextMatches(source, start, keyword) {
  const before = source.slice(0, start).trimEnd();

  // These positions come from the fixed demo grammar, not from generic
  // identifier spelling. In particular, `let t` is a complete IDENT and must
  // not be held merely because `t` is a prefix of `true`:
  //
  //   `l`, ` le`             -> pending `let`
  //   `let x: numb`          -> pending `number`
  //   `let x: number = tr`   -> pending `true`
  //   `let x: number = "x".le` -> pending `length`
  //   `let t`, `const n`     -> ordinary identifiers, never pending
  if (keyword === "let") return before.length === 0;
  if (["number", "string", "boolean"].includes(keyword)) return before.endsWith(":");
  if (["true", "false"].includes(keyword)) {
    return /(?:=|\(|\+|-|\*|\/|%|<)\s*$/u.test(before);
  }
  if (keyword === "length") return before.endsWith(".");
  return false;
}

function findOpenString(source) {
  let quote = null;
  let quoteStart = null;
  let escaped = false;

  for (let index = 0; index < source.length; index += 1) {
    const character = source[index];

    if (quote !== null) {
      if (escaped) {
        escaped = false;
      } else if (character === "\\") {
        escaped = true;
      } else if (character === quote) {
        quote = null;
        quoteStart = null;
      }
      continue;
    }

    if (character === '"' || character === "'") {
      quote = character;
      quoteStart = index;
    }
  }

  return quote === null ? null : quoteStart;
}

function normalizeRealizability(value) {
  if (value === true || value === "realizable") return "realizable";
  if (value === false || value === "unrealizable") return "unrealizable";
  return "unknown";
}

function statusLabelFor(status) {
  if (status === "realizable") return "Realizable";
  if (status === "unrealizable") return "Unrealizable";
  return "Unknown";
}

function setStatus(status, label) {
  statusBadge.className = `status-badge status-${status}`;
  statusLabel.textContent = label;
}

function setBusy(busy) {
  tokenStrip.setAttribute("aria-busy", String(busy));
  if (busy) {
    setStatus(workerReady ? "running" : "loading", workerReady ? "Analyzing prefix" : "Loading engine");
    totalTime.textContent = "…";
  }
}

function showError(message) {
  errorMessage.textContent = message;
  errorPanel.hidden = false;
}

function hideError() {
  errorPanel.hidden = true;
  errorMessage.textContent = "";
}

function formatError(error) {
  if (!error) return "Unknown analyzer error.";
  if (typeof error === "string") return error;
  return error.message || String(error);
}

function formatDuration(milliseconds) {
  if (milliseconds === null || !Number.isFinite(milliseconds)) return "—";
  if (milliseconds < 0.01) return "<0.01 ms";
  if (milliseconds < 1) return `${milliseconds.toFixed(2)} ms`;
  if (milliseconds < 100) return `${milliseconds.toFixed(1)} ms`;
  if (milliseconds < 1000) return `${Math.round(milliseconds)} ms`;
  return `${(milliseconds / 1000).toFixed(2)} s`;
}

function finiteNumber(value) {
  if (value === null || value === undefined || value === "") return null;
  const number = typeof value === "number" ? value : Number(value);
  return Number.isFinite(number) ? number : null;
}

function visibleLexeme(lexeme) {
  if (lexeme === "") return "ε";
  return lexeme.replaceAll("\n", "↵").replaceAll("\t", "⇥").replaceAll(" ", "␠");
}
