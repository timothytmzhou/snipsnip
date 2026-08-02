const VALID_SAMPLE = "let answer: number = 42;";
const INVALID_SAMPLE = "let answer: number = true;";
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
  const id = nextRequestId++;

  latestRequestId = id;
  requests.set(id, { version, source });
  pruneOldRequests(id);

  worker.postMessage({
    type: "analyze",
    id,
    program: programInput.value,
    source,
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
  const pending =
    result.pending && typeof result.pending === "object" ? result.pending : null;
  const fragment = document.createDocumentFragment();

  for (const token of tokens) {
    fragment.append(createToken(token, request.source));
  }

  if (pending) {
    fragment.append(createPendingToken(pending));
  }

  if (tokens.length === 0 && !pending) {
    const empty = document.createElement("div");
    empty.className = "token-empty";
    empty.textContent = "No lexemes yet · showing the result for ε";
    fragment.append(empty);
  }

  tokenStrip.replaceChildren(fragment);

  const elapsed = finiteNumber(result.totalMs) ?? finiteNumber(result.workerMs);
  totalTime.textContent = formatDuration(elapsed);

  if (pending) {
    setStatus("unknown", "Unknown · incomplete lexeme");
    traceHint.textContent = "The incomplete lexeme is held outside the parser until it is complete.";
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
  const lexeme = String(pending.lexeme ?? "");
  const button = document.createElement("button");
  button.type = "button";
  button.className = "token token-pending";
  button.title = "Incomplete lexeme";
  button.setAttribute("aria-label", `${visibleLexeme(lexeme)}, incomplete lexeme`);

  const lexemeElement = document.createElement("span");
  lexemeElement.className = "token-lexeme";
  lexemeElement.textContent = visibleLexeme(lexeme);

  const meta = document.createElement("span");
  meta.className = "token-meta";
  meta.textContent = "pending";

  button.append(lexemeElement, meta);
  return button;
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
