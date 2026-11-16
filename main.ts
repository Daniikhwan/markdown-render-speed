// main.ts — fast Markdown to HTML renderer.
// Node 22, standard library only. No network, no dependencies.
// Reads Markdown from a CLI file/dir argument, stdin, or /input/*.md
// (in that priority order) and writes HTML to stdout and, best effort,
// to /output/output.html. Single pass, deterministic: the same input
// always produces the same bytes.
//
// Written as plain JavaScript (no TypeScript annotations) so that both
// `node --check` and `node main.ts` work on stock Node 22/24.

import { readFileSync, writeFileSync, mkdirSync, readdirSync, existsSync, statSync } from "node:fs";

// ---------------- small helpers ----------------

function isSpace(c) {
  return c === 32 || c === 9 || c === 10 || c === 13 || c === 12 || c === 11;
}
function isAlnum(c) {
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c >= 128;
}
function isPunct(c) {
  return (c >= 33 && c <= 47) || (c >= 58 && c <= 64) || (c >= 91 && c <= 96) || (c >= 123 && c <= 126);
}
function isBlank(line) {
  for (let i = 0; i < line.length; i++) {
    const c = line.charCodeAt(i);
    if (c !== 32 && c !== 9 && c !== 13) return false;
  }
  return true;
}

// Escape &, <, > in text. Fast path when nothing needs escaping.
function escapeHtml(s) {
  if (s.indexOf("&") === -1 && s.indexOf("<") === -1 && s.indexOf(">") === -1) return s;
  let out = "";
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === 38) { out += s.slice(start, i) + "&amp;"; start = i + 1; }
    else if (c === 60) { out += s.slice(start, i) + "&lt;"; start = i + 1; }
    else if (c === 62) { out += s.slice(start, i) + "&gt;"; start = i + 1; }
  }
  return out + s.slice(start);
}

// Escape &, <, >, " for attribute values.
function escapeAttr(s) {
  if (s.indexOf("&") === -1 && s.indexOf("<") === -1 && s.indexOf(">") === -1 && s.indexOf('"') === -1) return s;
  let out = "";
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === 38) { out += s.slice(start, i) + "&amp;"; start = i + 1; }
    else if (c === 60) { out += s.slice(start, i) + "&lt;"; start = i + 1; }
    else if (c === 62) { out += s.slice(start, i) + "&gt;"; start = i + 1; }
    else if (c === 34) { out += s.slice(start, i) + "&quot;"; start = i + 1; }
  }
  return out + s.slice(start);
}

// ---------------- link reference definitions ----------------

let REFS = new Map();
const REF_DEF_RE = /^\[([^\]]+)\]:[ \t]*<?([^\s>]+)>?/;
function normRef(s) {
  return s.trim().toLowerCase().replace(/\s+/g, " ");
}

// Parse [text](url "title"), [text][ref] or [text] starting at s[i] === '['.
// Returns { text, url, title, end } or null.
function parseLink(s, i) {
  const n = s.length;
  let depth = 1;
  let j = i + 1;
  while (j < n) {
    const c = s.charCodeAt(j);
    if (c === 92) { j += 2; continue; }
    if (c === 91) depth++;
    else if (c === 93) { depth--; if (depth === 0) break; }
    j++;
  }
  if (j >= n) return null;
  const text = s.slice(i + 1, j);
  // Inline link: (url) or (url "title").
  if (j + 1 < n && s.charCodeAt(j + 1) === 40) {
    let k = j + 2;
    while (k < n && (s.charCodeAt(k) === 32 || s.charCodeAt(k) === 9)) k++;
    let url = "";
    if (k < n && s.charCodeAt(k) === 60) {
      const end = s.indexOf(">", k + 1);
      if (end === -1) return null;
      url = s.slice(k + 1, end);
      k = end + 1;
    } else {
      let d = 0;
      const start = k;
      while (k < n) {
        const c = s.charCodeAt(k);
        if (c === 40) d++;
        else if (c === 41) { if (d === 0) break; d--; }
        else if ((c === 32 || c === 9 || c === 10) && d === 0) break;
        k++;
      }
      url = s.slice(start, k);
    }
    while (k < n && (s.charCodeAt(k) === 32 || s.charCodeAt(k) === 9)) k++;
    let title = "";
    if (k < n && (s.charCodeAt(k) === 34 || s.charCodeAt(k) === 39)) {
      const q = s.charCodeAt(k);
      const end = s.indexOf(String.fromCharCode(q), k + 1);
      if (end !== -1) { title = s.slice(k + 1, end); k = end + 1; }
    }
    while (k < n && (s.charCodeAt(k) === 32 || s.charCodeAt(k) === 9)) k++;
    if (k >= n || s.charCodeAt(k) !== 41) return null;
    return { text, url, title, end: k + 1 };
  }
  // Full reference: [text][ref].
  if (j + 1 < n && s.charCodeAt(j + 1) === 91) {
    const end2 = s.indexOf("]", j + 2);
    if (end2 !== -1) {
      const url = REFS.get(normRef(s.slice(j + 2, end2)));
      if (url) return { text, url, title: "", end: end2 + 1 };
    }
  }
  // Shortcut reference: [text].
  const url = REFS.get(normRef(text));
  if (url) return { text, url, title: "", end: j + 1 };
  return null;
}

// ---------------- inline parser ----------------

const ENTITY_RE = /^&(#\d+|#x[0-9a-fA-F]+|[a-zA-Z][a-zA-Z0-9]+);/;
const AUTOLINK_SCHEME_RE = /^[a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\s<>]+$/;
const AUTOLINK_EMAIL_RE = /^[^\s@<>]+@[^\s@<>]+\.[^\s@<>]+$/;

// Close the top `partsRev.length` delimiter entries (must match, in order).
// partsRev lists kinds in closing order: last-opened first.
function closeRun(stack, out, partsRev) {
  if (stack.length < partsRev.length) return false;
  for (let p = 0; p < partsRev.length; p++) {
    if (stack[stack.length - 1 - p].kind !== partsRev[p]) return false;
  }
  for (const p of partsRev) {
    const entry = stack.pop();
    out[entry.idx] = p === 2 ? "<strong>" : "<em>";
    out.push(p === 2 ? "</strong>" : "</em>");
  }
  return true;
}

// Process a run of `*` (marker "*") or `_` (marker "_") starting at s[i],
// ending at s[j]. `out`/`stack` are the inline output and delimiter stack.
function processDelim(s, i, j, run, marker, out, stack, underscore) {
  const parts = [];
  let rem = run;
  while (rem >= 2) { parts.push(2); rem -= 2; }
  if (rem === 1) parts.push(1);
  const prevCh = i - 1;
  const nextCh = j;
  let canOpen, canClose;
  if (underscore) {
    const prevAlnum = prevCh >= 0 && isAlnum(s.charCodeAt(prevCh));
    const nextAlnum = nextCh < s.length && isAlnum(s.charCodeAt(nextCh));
    canOpen = nextCh < s.length && !isSpace(s.charCodeAt(nextCh)) && !prevAlnum;
    canClose = prevCh >= 0 && !isSpace(s.charCodeAt(prevCh)) && !nextAlnum;
  } else {
    canOpen = nextCh < s.length && !isSpace(s.charCodeAt(nextCh));
    canClose = prevCh >= 0 && !isSpace(s.charCodeAt(prevCh));
  }
  if (canClose) {
    const rev = parts.slice().reverse();
    if (closeRun(stack, out, rev)) return;
  }
  if (canOpen) {
    for (const p of parts) {
      stack.push({ kind: p, idx: out.length, marker: p === 2 ? marker + marker : marker });
      out.push("");
    }
  } else {
    out.push(s.slice(i, j));
  }
}

function renderInline(s) {
  const n = s.length;
  if (n === 0) return "";
  // Fast path: no inline markup characters at all. Such a string holds no
  // &, < or > either, so it needs no escaping and is returned as-is.
  if (s.indexOf("*") === -1 && s.indexOf("_") === -1 && s.indexOf("`") === -1 &&
      s.indexOf("[") === -1 && s.indexOf("!") === -1 && s.indexOf("\\") === -1 &&
      s.indexOf("&") === -1 && s.indexOf("<") === -1 && s.indexOf(">") === -1) return s;
  const out = [];
  const stack = [];
  let i = 0;
  let textStart = 0;
  while (i < n) {
    const c = s.charCodeAt(i);
    if (c === 42) { // '*'
      let j = i;
      while (j < n && s.charCodeAt(j) === 42) j++;
      if (i > textStart) out.push(s.slice(textStart, i));
      processDelim(s, i, j, j - i, "*", out, stack, false);
      i = j;
      textStart = i;
      continue;
    }
    if (c === 95) { // '_'
      let j = i;
      while (j < n && s.charCodeAt(j) === 95) j++;
      if (i > textStart) out.push(s.slice(textStart, i));
      processDelim(s, i, j, j - i, "_", out, stack, true);
      i = j;
      textStart = i;
      continue;
    }
    if (c === 96) { // '`' code span
      let j = i;
      while (j < n && s.charCodeAt(j) === 96) j++;
      const run = j - i;
      let close = -1;
      let p = s.indexOf("`", j);
      while (p !== -1) {
        let q = p;
        while (q < n && s.charCodeAt(q) === 96) q++;
        if (q - p === run) { close = p; break; }
        p = s.indexOf("`", q);
      }
      if (close !== -1) {
        if (i > textStart) out.push(s.slice(textStart, i));
        let code = s.slice(j, close);
        if (code.length >= 2 && code.charCodeAt(0) === 32 && code.charCodeAt(code.length - 1) === 32 && code.trim() !== "") {
          code = code.slice(1, -1);
        }
        out.push("<code>" + escapeHtml(code) + "</code>");
        i = close + run;
        textStart = i;
        continue;
      }
      i = j; // no closing backtick: literal, keep scanning
      continue;
    }
    if (c === 91) { // '[' link
      const parsed = parseLink(s, i);
      if (parsed) {
        if (i > textStart) out.push(s.slice(textStart, i));
        out.push('<a href="' + escapeAttr(parsed.url) + '"' +
          (parsed.title ? ' title="' + escapeAttr(parsed.title) + '"' : "") +
          ">" + renderInline(parsed.text) + "</a>");
        i = parsed.end;
        textStart = i;
        continue;
      }
      i++;
      continue;
    }
    if (c === 33) { // '!' image
      if (i + 1 < n && s.charCodeAt(i + 1) === 91) {
        const parsed = parseLink(s, i + 1);
        if (parsed) {
          if (i > textStart) out.push(s.slice(textStart, i));
          out.push('<img src="' + escapeAttr(parsed.url) + '" alt="' + escapeAttr(parsed.text) + '"' +
            (parsed.title ? ' title="' + escapeAttr(parsed.title) + '"' : "") + ">");
          i = parsed.end;
          textStart = i;
          continue;
        }
      }
      i++;
      continue;
    }
    if (c === 92) { // '\' backslash escape
      if (i + 1 < n && isPunct(s.charCodeAt(i + 1))) {
        if (i > textStart) out.push(s.slice(textStart, i));
        out.push(s[i + 1]);
        i += 2;
        textStart = i;
        continue;
      }
      i++;
      continue;
    }
    if (c === 38) { // '&' entity or escape
      const m = ENTITY_RE.exec(s.slice(i, i + 40));
      if (i > textStart) out.push(s.slice(textStart, i));
      if (m) { out.push(m[0]); i += m[0].length; }
      else { out.push("&amp;"); i += 1; }
      textStart = i;
      continue;
    }
    if (c === 60) { // '<' autolink or escape
      const j = s.indexOf(">", i + 1);
      if (j !== -1 && j - i < 300) {
        const inner = s.slice(i + 1, j);
        if (AUTOLINK_SCHEME_RE.test(inner) || AUTOLINK_EMAIL_RE.test(inner)) {
          if (i > textStart) out.push(s.slice(textStart, i));
          const href = inner.indexOf("@") !== -1 && inner.indexOf(":") === -1 ? "mailto:" + inner : inner;
          out.push('<a href="' + escapeAttr(href) + '">' + escapeHtml(inner) + "</a>");
          i = j + 1;
          textStart = i;
          continue;
        }
      }
      if (i > textStart) out.push(s.slice(textStart, i));
      out.push("&lt;");
      i++;
      textStart = i;
      continue;
    }
    if (c === 62) { // '>'
      if (i > textStart) out.push(s.slice(textStart, i));
      out.push("&gt;");
      i++;
      textStart = i;
      continue;
    }
    i++;
  }
  if (n > textStart) out.push(s.slice(textStart, n));
  // Unclosed delimiters become literal text.
  for (let t = stack.length - 1; t >= 0; t--) {
    out[stack[t].idx] = stack[t].marker;
  }
  return out.join("");
}

// ---------------- block parser ----------------

function fenceStart(line) {
  let i = 0;
  while (i < line.length && line.charCodeAt(i) === 32) i++;
  if (i >= line.length) return null;
  const c = line.charCodeAt(i);
  if (c !== 96 && c !== 126) return null;
  let len = 0;
  while (i + len < line.length && line.charCodeAt(i + len) === c) len++;
  if (len < 3) return null;
  let info = line.slice(i + len).trim();
  const sp = info.search(/\s/);
  if (sp !== -1) info = info.slice(0, sp);
  return { ch: c, len, info };
}
function isFenceEnd(line, fence) {
  let i = 0;
  while (i < line.length && line.charCodeAt(i) === 32) i++;
  let len = 0;
  while (i + len < line.length && line.charCodeAt(i + len) === fence.ch) len++;
  if (len < fence.len) return false;
  for (let j = i + len; j < line.length; j++) {
    const d = line.charCodeAt(j);
    if (d !== 32 && d !== 9) return false;
  }
  return true;
}
function atxHeading(line) {
  let i = 0;
  while (i < line.length && line.charCodeAt(i) === 32) i++;
  if (i >= line.length || line.charCodeAt(i) !== 35) return null;
  let level = 0;
  while (i < line.length && line.charCodeAt(i) === 35) { level++; i++; }
  if (level > 6) return null;
  if (i < line.length && line.charCodeAt(i) !== 32 && line.charCodeAt(i) !== 9) return null;
  while (i < line.length && (line.charCodeAt(i) === 32 || line.charCodeAt(i) === 9)) i++;
  let text = line.slice(i);
  let e = text.length;
  while (e > 0 && (text.charCodeAt(e - 1) === 32 || text.charCodeAt(e - 1) === 9)) e--;
  text = text.slice(0, e);
  let f = e;
  while (f > 0 && text.charCodeAt(f - 1) === 35) f--;
  if (f < e && f > 0 && (text.charCodeAt(f - 1) === 32 || text.charCodeAt(f - 1) === 9)) {
    let g = f;
    while (g > 0 && (text.charCodeAt(g - 1) === 32 || text.charCodeAt(g - 1) === 9)) g--;
    text = text.slice(0, g);
  }
  return { level, text };
}
function isHr(line) {
  let i = 0;
  while (i < line.length && (line.charCodeAt(i) === 32 || line.charCodeAt(i) === 9)) i++;
  if (i >= line.length) return false;
  const c = line.charCodeAt(i);
  if (c !== 45 && c !== 95 && c !== 42) return false;
  let count = 0;
  for (let j = i; j < line.length; j++) {
    const d = line.charCodeAt(j);
    if (d === c) count++;
    else if (d !== 32 && d !== 9) return false;
  }
  return count >= 3;
}
function setextLevel(line) {
  let i = 0;
  while (i < line.length && (line.charCodeAt(i) === 32 || line.charCodeAt(i) === 9)) i++;
  if (i >= line.length) return 0;
  const c = line.charCodeAt(i);
  if (c !== 61 && c !== 45) return 0;
  for (let j = i + 1; j < line.length; j++) {
    const d = line.charCodeAt(j);
    if (d !== c && d !== 32 && d !== 9) return 0;
  }
  return c === 61 ? 1 : 2;
}
// Returns { ordered, width } for a list marker at the start of `line`, else null.
function listMarker(line) {
  const c0 = line.charCodeAt(0);
  if (c0 === 45 || c0 === 42 || c0 === 43) {
    if (line.length === 1) return { ordered: false, width: 1 };
    const c1 = line.charCodeAt(1);
    if (c1 === 32 || c1 === 9) return { ordered: false, width: 2 };
    return null;
  }
  if (c0 >= 48 && c0 <= 57) {
    let i = 0;
    while (i < line.length && line.charCodeAt(i) >= 48 && line.charCodeAt(i) <= 57) i++;
    if (i === 0 || i > 9) return null;
    const d = line.charCodeAt(i);
    if (d !== 46 && d !== 41) return null;
    if (i + 1 >= line.length) return { ordered: true, width: i + 1 };
    const c1 = line.charCodeAt(i + 1);
    if (c1 === 32 || c1 === 9) return { ordered: true, width: i + 2 };
    return null;
  }
  return null;
}
// Strip one level of list-item indentation (up to 2 spaces, or one tab).
function stripIndent(cl) {
  if (cl.charCodeAt(0) === 9) return cl.slice(1);
  let k = 0;
  while (k < cl.length && k < 2 && cl.charCodeAt(k) === 32) k++;
  return cl.slice(k);
}
// Unwrap a single outer <p>...</p> (kept for reference; the tight flag in
// renderBlocks now suppresses <p> on list-item paragraphs directly).
function unwrapSingleP(html) {
  if (html.startsWith("<p>") && html.endsWith("</p>") && html.indexOf("<p>", 3) === -1) {
    return html.slice(3, -4);
  }
  return html;
}

// `tight` is true when rendering the blocks of a tight list item: its
// paragraphs are emitted without <p> wrappers, per CommonMark.
function renderBlocks(lines, tight) {
  const out = [];
  let i = 0;
  const n = lines.length;
  while (i < n) {
    const line = lines[i];
    if (isBlank(line)) { i++; continue; }
    const fence = fenceStart(line);
    if (fence) {
      const buf = [];
      i++;
      while (i < n && !isFenceEnd(lines[i], fence)) { buf.push(lines[i]); i++; }
      if (i < n) i++;
      const cls = fence.info ? ' class="language-' + escapeAttr(fence.info) + '"' : "";
      out.push("<pre><code" + cls + ">" + escapeHtml(buf.join("\n")) + "</code></pre>");
      continue;
    }
    const h = atxHeading(line);
    if (h) {
      out.push("<h" + h.level + ">" + renderInline(h.text) + "</h" + h.level + ">");
      i++;
      continue;
    }
    if (isHr(line)) { out.push("<hr>"); i++; continue; }
    if (line.charCodeAt(0) === 62) { // '>' blockquote
      const inner = [];
      while (i < n && lines[i].charCodeAt(0) === 62) {
        const l = lines[i];
        inner.push(l.length > 1 && l.charCodeAt(1) === 32 ? l.slice(2) : l.slice(1));
        i++;
      }
      out.push("<blockquote>" + renderBlocks(inner, false).join("\n") + "</blockquote>");
      continue;
    }
    const lm = listMarker(line);
    if (lm) {
      const tag = lm.ordered ? "ol" : "ul";
      const items = [];
      let listTight = true;
      while (i < n) {
        const m = listMarker(lines[i]);
        if (!m || m.ordered !== lm.ordered) break;
        const itemLines = [lines[i].slice(m.width)];
        i++;
        while (i < n) {
          const cl = lines[i];
          if (isBlank(cl)) {
            let j = i;
            while (j < n && isBlank(lines[j])) j++;
            if (j < n) {
              const nm = listMarker(lines[j]);
              if (nm && nm.ordered === lm.ordered) { listTight = false; i = j; break; }
            }
            i = j;
            break;
          }
          if (listMarker(cl)) break;
          if (cl.charCodeAt(0) === 32 || cl.charCodeAt(0) === 9) {
            itemLines.push(stripIndent(cl));
            i++;
            continue;
          }
          break;
        }
        items.push(itemLines);
      }
      let html = "<" + tag + ">";
      for (const itemLines of items) {
        html += "<li>" + renderBlocks(itemLines, listTight).join("\n") + "</li>";
      }
      html += "</" + tag + ">";
      out.push(html);
      continue;
    }
    // Paragraph (may become a setext heading).
    const para = [];
    let headingLevel = 0;
    while (i < n) {
      const cl = lines[i];
      if (isBlank(cl)) break;
      const st = setextLevel(cl);
      if (st && para.length > 0) { headingLevel = st; i++; break; }
      if (fenceStart(cl) || atxHeading(cl) || isHr(cl) || cl.charCodeAt(0) === 62 || listMarker(cl)) break;
      para.push(cl);
      i++;
    }
    if (para.length > 0) {
      if (headingLevel) out.push("<h" + headingLevel + ">" + renderInline(para.join("\n")) + "</h" + headingLevel + ">");
      else if (tight) out.push(renderInline(para.join("\n")));
      else out.push("<p>" + renderInline(para.join("\n")) + "</p>");
    }
  }
  return out;
}

// ---------------- top-level render ----------------

function render(md) {
  const text = md.replace(/\r\n?/g, "\n");
  const rawLines = text.split("\n");
  REFS = new Map();
  const lines = [];
  for (const line of rawLines) {
    if (line.charCodeAt(0) === 91) {
      const m = REF_DEF_RE.exec(line);
      if (m) { REFS.set(normRef(m[1]), m[2]); continue; }
    }
    lines.push(line);
  }
  const blocks = renderBlocks(lines);
  return blocks.length ? blocks.join("\n") + "\n" : "";
}

// ---------------- input / output ----------------

function readInput() {
  const args = process.argv.slice(2).filter((a) => a.charAt(0) !== "-");
  // 1. CLI file or directory argument(s).
  for (const a of args) {
    try {
      const st = statSync(a);
      if (st.isFile()) return readFileSync(a, "utf8");
      if (st.isDirectory()) {
        const files = readdirSync(a).filter((f) => f.endsWith(".md") || f.endsWith(".markdown")).sort();
        if (files.length) return files.map((f) => readFileSync(a + "/" + f, "utf8")).join("\n");
      }
    } catch (e) { /* not a readable path: try the next source */ }
  }
  // 2. stdin, when piped.
  if (!process.stdin.isTTY) {
    try {
      const data = readFileSync(0, "utf8");
      if (data) return data;
    } catch (e) { /* fall through */ }
  }
  // 3. /input: /input/input.md, then any *.md, then any file.
  try {
    if (existsSync("/input/input.md")) return readFileSync("/input/input.md", "utf8");
    if (existsSync("/input")) {
      const st = statSync("/input");
      if (st.isDirectory()) {
        const files = readdirSync("/input").filter((f) => f.endsWith(".md") || f.endsWith(".markdown") || f.endsWith(".txt")).sort();
        if (files.length) return files.map((f) => readFileSync("/input/" + f, "utf8")).join("\n");
        const all = readdirSync("/input").sort();
        const parts = [];
        for (const f of all) {
          try {
            if (statSync("/input/" + f).isFile()) parts.push(readFileSync("/input/" + f, "utf8"));
          } catch (e) { /* skip */ }
        }
        if (parts.length) return parts.join("\n");
      } else if (st.isFile()) {
        return readFileSync("/input", "utf8");
      }
    }
  } catch (e) { /* fall through */ }
  return "";
}

function main() {
  const html = render(readInput());
  process.stdout.write(html);
  try {
    mkdirSync("/output", { recursive: true });
    writeFileSync("/output/output.html", html);
  } catch (e) { /* stdout is the primary channel */ }
  try {
    writeFileSync("/output/entry.html", html);
  } catch (e) { /* ignore */ }
}

main();
