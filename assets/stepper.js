/* proofbook stepper: renders a rocqtui proof trace (format v1).
   Runs in the page; the pure parts (layout engine, tokenizer) are
   also exported for node tests. */
(function (root) {
'use strict';

/* ---------- Pp layout engine ----------------------------------------
   A small Format-style pretty printer over the trace's structured Pp
   documents: string | [doc…] | {b,i,d} | {t,d} | {brk:[n,off]} | {nl:1}.
   Boxes: h never breaks; v breaks at every hint; hv breaks at every
   hint iff the box does not fit; hov breaks a hint only when the
   material up to the next hint does not fit (fill). New lines inside
   a box are indented to the column the box opened at, plus the box
   indent, plus the hint offset. */

const COMBINING = /[̀-ͯ᪰-᫿᷀-᷿⃐-⃿︀-️]/;
function width(s) {
  let w = 0;
  for (const ch of s) if (!COMBINING.test(ch)) w++;
  return w;
}

const flatMemo = new WeakMap();
function flat(doc) {
  if (typeof doc === 'string') return width(doc);
  if (flatMemo.has(doc)) return flatMemo.get(doc);
  let w;
  if (Array.isArray(doc)) { w = 0; for (const d of doc) w += flat(d); }
  else if (doc.brk) w = doc.brk[0];
  else if (doc.nl) w = Infinity;
  else w = flat(doc.d);
  flatMemo.set(doc, w);
  return w;
}

function tagClass(t) {
  return 'pp-' + t.replace(/^constr\./, '').replace(/\./g, '-');
}

/* Width of the material after index k up to the next break hint at
   this level (nested boxes count flat). */
function chunk(items, k) {
  let w = 0;
  for (let j = k; j < items.length; j++) {
    const it = items[j];
    if (it && it.brk) break;
    w += flat(it);
    if (w === Infinity) break;
  }
  return w;
}

function layout(doc, W) {
  const st = { lines: [[]], col: 0 };
  const emit = (text, cls) => {
    if (!text) return;
    st.lines[st.lines.length - 1].push({ text, cls });
    st.col += width(text);
  };
  const newline = (indent) => {
    st.lines.push([]);
    st.col = 0;
    emit(' '.repeat(Math.max(0, indent)), null);
  };
  function render(d, box, cls) {
    if (typeof d === 'string') return emit(d, cls);
    if (Array.isArray(d)) {
      for (let k = 0; k < d.length; k++) {
        const it = d[k];
        if (it && it.brk) {
          const [n, off] = it.brk;
          if (!box.broken) emit(' '.repeat(n), null);
          else if (box.type === 'hov') {
            if (st.col + n + chunk(d, k + 1) > W) newline(box.indent + off);
            else emit(' '.repeat(n), null);
          } else newline(box.indent + off);
        } else render(it, box, cls);
      }
      return;
    }
    if (d.nl) return newline(box.indent);
    if (d.t !== undefined) return render(d.d, box, cls + ' ' + tagClass(d.t));
    if (d.b !== undefined) {
      const start = st.col;
      const fits = start + flat(d.d) <= W;
      const broken = d.b === 'v' ? true : d.b === 'h' ? false : !fits;
      return render(d.d, { type: d.b, indent: start + d.i, broken }, cls);
    }
    if (d.brk) {  // a lone break hint outside an array
      return render([d], box, cls);
    }
  }
  render(doc, { type: 'hov', indent: 0, broken: flat(doc) > W }, '');
  return st.lines;
}

function linesToText(lines) {
  return lines.map(l => l.map(s => s.text).join('')).join('\n');
}

/* ---------- Source tokenizer -----------------------------------------
   Enough for colouring: nested comments, strings, numbers, identifiers
   (Unicode letters, dotted qualification) classified by the rocqtui
   keyword lists. Returns [{s, e, cls}] covering [s, e) without gaps. */

const TACTICS = new Set(("intros intro apply exact rewrite simpl unfold destruct induction " +
  "inversion split left right exists reflexivity symmetry transitivity assumption " +
  "contradiction discriminate injection auto eauto omega lia ring field tauto " +
  "firstorder trivial congruence subst clear rename assert pose set remember " +
  "generalize specialize revert case elim constructor econstructor eapply replace " +
  "change pattern cbv lazy compute vm_compute native_compute cbn hnf red fold cut " +
  "enough exfalso f_equal decide now easy solve try repeat progress do only idtac " +
  "fail abstract shelve unshelve move have suff wlog congr lazymatch multimatch " +
  "first tryif once exactly_once timeout match with").split(' '));

const VERNAC = new Set(("Theorem Lemma Definition Fixpoint CoFixpoint Inductive CoInductive " +
  "Record Structure Module Section End Require Import Export Open Close Scope " +
  "Notation Infix Set Unset Check Print Compute Eval Search About Proof Qed Defined " +
  "Admitted Abort Let Example Fact Corollary Proposition Variable Variables " +
  "Hypothesis Hypotheses Context Existing Instance Class Ltac Ltac2 Canonical " +
  "Coercion Universe Universes Sort Sorts Program Next Obligation Goal Local Global " +
  "Cumulative NonCumulative Monomorphic Polymorphic Fail Succeed Time Redirect " +
  "Arguments Implicit Declare Typeclasses Opaque Transparent Scheme Combined " +
  "Extract Extraction Add Load Comments Bind Delimit Hint Resolve Immediate " +
  "Constructors Unfold Rewrite Extern Mode Cut Reserved Tactic Parameter Parameters " +
  "Axiom Axioms Conjecture Register Include Type Prop SProp Type forall fun let in " +
  "match with end if then else fix cofix return as using where").split(' '));

const IDENT = /[\p{L}_][\p{L}\p{N}_']*(?:\.[\p{L}_][\p{L}\p{N}_']*)*/uy;
const NUMBER = /[0-9]+/y;

function tokenize(src, s, e) {
  const out = [];
  let i = s;
  const push = (to, cls) => { if (to > i) { out.push({ s: i, e: to, cls }); i = to; } };
  while (i < e) {
    const c = src[i];
    if (c === '(' && src[i + 1] === '*') {
      let depth = 1, j = i + 2;
      while (j < e && depth > 0) {
        if (src[j] === '(' && src[j + 1] === '*') { depth++; j += 2; }
        else if (src[j] === '*' && src[j + 1] === ')') { depth--; j += 2; }
        else j++;
      }
      push(Math.min(j, e), 'comment');
    } else if (c === '"') {
      let j = i + 1;
      while (j < e) {
        if (src[j] === '"') { if (src[j + 1] === '"') j += 2; else { j++; break; } }
        else j++;
      }
      push(Math.min(j, e), 'string');
    } else {
      IDENT.lastIndex = i;
      let m = IDENT.exec(src);
      if (m && m.index === i) {
        const to = Math.min(i + m[0].length, e);
        const word = src.slice(i, to);
        const cls = VERNAC.has(word) ? 'vernac' : TACTICS.has(word) ? 'tactic' : 'ident';
        push(to, cls);
        continue;
      }
      NUMBER.lastIndex = i;
      m = NUMBER.exec(src);
      if (m && m.index === i) { push(Math.min(i + m[0].length, e), 'number'); continue; }
      // plain run up to the next interesting code point (surrogate
      // pairs: index by code point, not code unit)
      let j = i + String.fromCodePoint(src.codePointAt(i)).length;
      while (j < e) {
        const ch = String.fromCodePoint(src.codePointAt(j));
        if (/[\p{L}_"(0-9]/u.test(ch)) break;
        j += ch.length;
      }
      push(j, null);
    }
  }
  return out;
}

/* ---------- Explode trees ---------------------------------------------
   Preorder flattening of a recorded piece tree: one row per node with
   its depth, ordinal among its siblings, range, goals, error, and the
   goals before it (its parent's) for change marking. */
function flattenExplode(tree, before) {
  const rows = [];
  (function walk(node, depth, ordinal, prevGoals) {
    rows.push({ depth, ordinal, s: node.s, e: node.e, goals: node.goals, error: node.error, prev: prevGoals });
    const n = node.children.length;
    node.children.forEach((c, j) => walk(c.tree, depth + 1, n > 1 ? [j + 1, n] : null, node.goals));
  })(tree, 0, null, before);
  return rows;
}

/* ---------- Gloss ------------------------------------------------------
   The gloss (docs/GLOSS_PLAN.md) places text on items: a definition's
   sentence and, for a lemma, the proof sentences after it. The item at
   sentence i is the last one starting at or before i whose range
   reaches i; sentences between items belong to the file summary. */
const KIND_LABELS = { ltac: 'tactic', tacn: 'tactic notation', coercion: 'coercion declaration',
  canonical: 'canonical structure', existing_instance: 'existing instance', let: 'section-local' };
function kindLabel(k) { return KIND_LABELS[k] || k || ''; }

function glossItemAt(items, i) {
  let found = null;
  for (const it of items) {
    if (it.start > i) break;
    if (it.also && it.also.includes(i)) return it;   // a notation's variant, a redefinition
    found = it;
  }
  if (!found) return null;
  const last = found.body ? found.body[1] : found.start;
  return i <= last ? found : null;
}

/* Prose with [[name]] markers (links, resolved by the caller: name ->
   {href, full} or null), `code` spans, blank-line paragraphs, and
   fenced ```tikzcd blocks: figures when [diagrams] ({svg: {key: svg},
   err: {key: message}}, keyed as diagrams.py does) has a rendering,
   else the source in a code block. */
const FENCE_RE = /^```tikzcd([^\n]*)\n([\s\S]*?)^```[ \t]*$/gm;
function diagramKey(opts, body) {
  opts = opts.trim();
  if (opts.startsWith('[') && opts.endsWith(']')) opts = opts.slice(1, -1).trim();
  return opts + '\n' + body.replace(/\s+$/, '');
}
function renderProse(text, resolve, diagrams) {
  const esc = (s) => s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
  const inline = (t) => esc(t)
    .replace(/\[\[([^\]]+)\]\]/g, (m, name) => {
      const base = name.split('.').pop();
      const r = resolve(name);
      if (!r) return '<span class="mk">' + base + '</span>';
      return '<a class="mk" href="' + esc(r.href) + '" data-full="' + esc(r.full) + '">' + base + '</a>';
    })
    .replace(/`([^`]+)`/g, '<code>$1</code>');
  const paragraphs = (t) => t.split(/\n\s*\n/).map(p => p.trim()).filter(p => p)
    .map(p => '<p>' + inline(p) + '</p>').join('');
  const figure = (opts, body) => {
    const key = diagramKey(opts, body);
    const svg = diagrams && diagrams.svg && diagrams.svg[key];
    if (svg) return '<figure class="diagram">' + svg + '</figure>';
    const err = diagrams && diagrams.err && diagrams.err[key];
    return '<figure class="diagram source' + (err ? ' failed' : '') + '"><pre>' + esc(body.replace(/\s+$/, '')) + '</pre>'
      + (err ? '<div class="gstatus">diagram failed: ' + esc(err) + '</div>' : '') + '</figure>';
  };
  let out = '', last = 0, m;
  FENCE_RE.lastIndex = 0;
  while ((m = FENCE_RE.exec(text))) {
    out += paragraphs(text.slice(last, m.index)) + figure(m[1], m[2]);
    last = m.index + m[0].length;
  }
  return out + paragraphs(text.slice(last));
}

/* ---------- Page ------------------------------------------------------ */

function escapeHtml(s) {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

function main() {
  const data = JSON.parse(document.getElementById('data').textContent);
  const src = data.source, S = data.sentences, PP = data.pp;
  const srcEl = document.getElementById('src');
  const goalPre = document.getElementById('goalpre');
  const msgEl = document.getElementById('messages');
  const posEl = document.getElementById('pos');
  const kindEl = document.getElementById('kind');
  const msEl = document.getElementById('ms');
  let cur = -1;
  let allHyps = false;
  let usesOpen = false, vocabOpen = false;
  try { usesOpen = localStorage.getItem('usesOpen') === '1'; vocabOpen = localStorage.getItem('vocabOpen') === '1'; } catch (e) {}
  const freq = data.freq || {};
  const isFact = (u) => u.kind === 'lemma' || u.kind === 'instance';
  let xrows = null;      // explode rows of the current sentence when in explode mode
  let xsel = 0;
  const hintEl = document.getElementById('hint');
  const usesEl = document.getElementById('uses');
  const lib = data.meta.library || null;
  /* --- source pane --- */
  const refAt = new Map();
  for (const r of data.refs) refAt.set(r.s, r);
  const defAt = new Map();
  for (const d of data.defs) defAt.set(d.s, d);
  const defNames = new Set(data.defs.map(d => d.name));

  const G = data.gloss || null;
  const glossEl = document.getElementById('glossbody');
  let glossOpen = !!G;
  try { const v = localStorage.getItem('glossOpen'); if (v !== null) glossOpen = v === '1'; } catch (e) {}
  document.body.classList.toggle('gloss', glossOpen);
  const root = data.meta.root || null, libs = data.libs || {};
  const fullOf = (library, m, name) => library + '.' + (m ? m + '.' : '') + name;
  // The site page (relative to the site root) that defines a dotted path.
  function pageOfLib(path) {
    const parts = path.split('.');
    for (let n = parts.length; n > 0; n--) {
      const p = libs[parts.slice(0, n).join('.')];
      if (p) return p;
    }
    return null;
  }
  // A [[name]] marker in prose: a base name defined here, or a full path.
  function resolveName(name) {
    if (libs[name] && root) return { href: root + '/' + libs[name], full: name };
    const base = name.split('.').pop();
    if (defNames.has(base) && (!name.includes('.') || (lib && name.startsWith(lib + '.'))))
      return { href: '#def-' + base, full: lib ? lib + '.' + base : base };
    if (name.includes('.') && root) {
      const p = pageOfLib(name.slice(0, name.lastIndexOf('.')));
      if (p) return { href: root + '/' + p + '#def-' + base, full: name };
    }
    return null;
  }


  function pieceCuts(tree, acc) {
    acc.add(tree.s); acc.add(tree.e);
    for (const c of tree.children) pieceCuts(c.tree, acc);
    return acc;
  }
  function splitAt(tokens, cuts) {
    const out = [];
    for (const t of tokens) {
      let s = t.s;
      for (const c of cuts) if (c > s && c < t.e) { out.push({ s, e: c, cls: t.cls }); s = c; }
      out.push({ s, e: t.e, cls: t.cls });
    }
    return out;
  }
  function tokensHtml(s, e, cuts) {
    let h = '';
    let toks = tokenize(src, s, e);
    if (cuts) toks = splitAt(toks, [...cuts].sort((a, b) => a - b));
    for (const t of toks) {
      const text = escapeHtml(src.slice(t.s, t.e));
      const wrap = cuts ? (inner) => '<span class="pc" data-s="' + t.s + '" data-e="' + t.e + '">' + inner + '</span>' : (x) => x;
      // tactic names (and a notation's literal), and the first word of a
      // sentence defining an anonymous instance, carry links too
      if (t.cls === 'ident' || ((t.cls === 'tactic' || t.cls === 'string' || t.cls === 'vernac') && (defAt.has(t.s) || refAt.has(t.s)))) {
        const d = defAt.get(t.s), r = refAt.get(t.s);
        if (r && r.kind === 'lib') {
          // a module named on a Require line: its page, its gloss behind a popover
          const dm = ' data-mod="' + escapeHtml(r.lib) + '"';
          h += wrap(r.page ? '<a class="ref mod" href="' + escapeHtml(r.page) + '"' + dm + '>' + text + '</a>'
            : '<span class="ref-ext" title="' + escapeHtml(r.lib) + '"' + dm + '>' + text + '</span>');
          continue;
        }
        const full = r ? fullOf(r.lib, r.m, r.name) : d && lib ? fullOf(lib, d.m, d.name) : null;
        const df = full ? ' data-full="' + escapeHtml(full) + '"' : '';
        if (d) h += wrap('<span id="def-' + escapeHtml(d.name) + '" class="def"' + df + '>' + text + '</span>');
        else if (r && r.local && defNames.has(r.name))
          h += wrap('<a class="ref" href="#def-' + escapeHtml(r.name) + '"' + df + '>' + text + '</a>');
        else if (r && r.page)
          h += wrap('<a class="ref" href="' + escapeHtml(r.page) + '#def-' + escapeHtml(r.name.split('.').pop()) + '" title="' + escapeHtml(full) + '"' + df + '>' + text + '</a>');
        else if (r && !r.local)
          h += wrap('<span class="ref-ext" title="' + escapeHtml(full) + '"' + df + '>' + text + '</span>');
        else h += wrap(text);
      } else if (t.cls) h += wrap('<span class="tk-' + t.cls + '">' + text + '</span>');
      else h += wrap(text);
    }
    return h;
  }

  function buildSource() {
    let h = '', pos = 0;
    S.forEach((st, i) => {
      h += escapeHtml(src.slice(pos, st.s));
      const err = typeof st.status === 'object' ? ' err' : '';
      const ex = st.explode && st.explode.tree ? st.explode : null;
      const cuts = ex ? pieceCuts(ex.tree, new Set()) : null;
      h += '<span class="sent k-' + st.kind + err + (ex ? ' chain' : '') + '" data-i="' + i + '">' + tokensHtml(st.s, st.e, cuts) + '</span>';
      pos = st.e;
    });
    h += escapeHtml(src.slice(pos));
    srcEl.innerHTML = h;
  }

  /* --- goals pane --- */
  let charW = 7;
  function measure() {
    const probe = document.createElement('span');
    probe.textContent = 'M'.repeat(50);
    probe.style.visibility = 'hidden';
    goalPre.appendChild(probe);
    charW = probe.getBoundingClientRect().width / 50 || 7;
    probe.remove();
  }
  function cols() {
    const cs = getComputedStyle(goalPre);
    const pad = parseFloat(cs.paddingLeft) + parseFloat(cs.paddingRight);
    return Math.max(20, Math.floor((goalPre.clientWidth - pad) / charW));
  }

  function docHtml(id, W, indent, cls) { return docLinesHtml(PP[id], W, indent, cls); }
  function docLinesHtml(doc, W, indent, cls) {
    const lines = layout(doc, W - indent);
    const pad = ' '.repeat(indent);
    return lines.map((l, k) =>
      '<span class="' + cls + '">' + pad + l.map(s =>
        s.cls ? '<span class="' + s.cls.trim() + '">' + escapeHtml(s.text) + '</span>' : escapeHtml(s.text)
      ).join('') + '</span>'
    ).join('\n');
  }

  function goalsHtml(st, prev) {
    const W = cols();
    if (typeof st.status === 'object')
      return '<span class="gerr">' + escapeHtml(linesToText(layout(PP[st.status.error], W))) + '</span>';
    const g = st.goals;
    if (!g) return '<span class="gnote">(no proof in progress)</span>';
    const prevHyps = new Set(), prevCcl = prev && prev.goals && prev.goals.fg[0] ? prev.goals.fg[0].ccl : null;
    if (prev && prev.goals && prev.goals.fg[0]) for (const h of prev.goals.fg[0].hyps) prevHyps.add(h);
    const sep = (annot) => '<span class="sep">  ' + '_'.repeat(Math.max(10, Math.min(38, W - 12))) + annot + '</span>';
    const annotOf = (goal, i, n) => goal.name ? '(?' + escapeHtml(goal.name) + ')' : n > 1 ? '(' + (i + 1) + '/' + n + ')' : '';
    const parts = [];
    const fg = g.fg;
    if (fg.length === 0) {
      const bg = [].concat(...g.bg.map(([l, r]) => l.concat(r)));
      if (bg.length === 0 && g.shelved.length === 0 && g.given_up.length === 0)
        parts.push('<span class="gnote">No more subgoals.</span>');
      else if (bg.length === 0 && g.shelved.length === 0) {
        parts.push('<span class="gnote">All goals completed except some admitted goals:</span>', '');
        for (const goal of g.given_up) parts.push(docHtml(goal.ccl, W, 2, 'ccl'));
      } else if (bg.length === 0) {
        parts.push('<span class="gnote">All remaining goals are on the shelf:</span>', '');
        for (const goal of g.shelved) parts.push(docHtml(goal.ccl, W, 2, 'ccl'));
      } else {
        parts.push('<span class="gnote">This subproof is complete, but there are unfocused goals:</span>', '');
        bg.forEach((goal, i) => {
          parts.push(sep(annotOf(goal, i, bg.length)), docHtml(goal.ccl, W, 2, 'ccl'), '');
        });
      }
    } else {
      parts.push('<span class="gnote">' + fg.length + ' subgoal' + (fg.length > 1 ? 's' : '') + '</span>', '');
      fg.forEach((goal, i) => {
        if (i === 0 || allHyps)
          for (const h of goal.hyps)
            parts.push(docHtml(h, W, 2, 'hyp' + (i === 0 && !prevHyps.has(h) ? ' new' : '')));
        parts.push(sep(annotOf(goal, i, fg.length)));
        parts.push(docHtml(goal.ccl, W, 2, 'ccl' + (i === 0 && prevCcl !== goal.ccl ? ' new' : '')), '');
      });
    }
    return parts.join('\n');
  }

  function messagesHtml(st) {
    if (!st.messages.length) return '';
    const W = cols();
    return '<h4>Messages</h4>' + st.messages.map(id =>
      '<pre>' + escapeHtml(linesToText(layout(PP[id], W))) + '</pre>').join('');
  }

  // A used constant: its name linked, then its one-line description
  // from the constants table, filled in as the slice arrives.
  function useRow(u) {
    const k = u.name.lastIndexOf('.');
    const base = k >= 0 ? u.name.slice(k + 1) : u.name, dir = k >= 0 ? u.name.slice(0, k) : '';
    const inFile = lib && dir === lib && defNames.has(base);
    const df = ' data-full="' + escapeHtml(u.name) + '"';
    const nameHtml = inFile ? '<a href="#def-' + escapeHtml(base) + '"' + df + '>' + escapeHtml(base) + '</a>'
      : u.page ? '<a href="' + escapeHtml(u.page) + '#def-' + escapeHtml(base) + '" title="' + escapeHtml(u.name) + '"' + df + '>' + escapeHtml(base) + '</a>'
      : '<span title="' + escapeHtml(u.name) + '"' + df + '>' + escapeHtml(base) + '</span>';
    return '<tr class="' + (u.explicit ? 'exp' : 'hid') + '"><td class="name">' + nameHtml + '</td>'
      + '<td class="desc" data-desc="' + escapeHtml(u.name) + '"></td></tr>';
  }
  async function fillUseDescriptions() {
    const cells = usesEl.querySelectorAll('td.desc[data-desc]');
    for (const cell of cells) {
      const row = await lookup(cell.dataset.desc);
      if (!cell.isConnected) return;   // the step changed meanwhile
      cell.textContent = row && row.short ? txt(row.short) : (row === undefined ? '' : '');
    }
  }

  function usesHtml(st) {
    if (!st.uses) return '';
    // Facts the step applied, rare ones first, hidden before named;
    // the vocabulary it manipulated is a count unless opened.
    const byRarity = (a, b) => (freq[a.name] || 0) - (freq[b.name] || 0);
    const facts = st.uses.filter(isFact), vocab = st.uses.filter(u => !isFact(u));
    const hidden = facts.filter(u => !u.explicit).sort(byRarity), named = facts.filter(u => u.explicit);
    const summary = st.uses.length === 0 ? 'nothing new in the proof term'
      : (facts.length === 0 ? 'no lemma or instance' : hidden.length + ' hidden' + (named.length ? ', ' + named.length + ' named' : ''))
        + (vocab.length ? ' · ' + vocab.length + ' vocabulary' : '');
    let h = '<div class="uhead" id="uhead">' + (usesOpen ? '▾' : '▸') + ' used by this step' + (usesOpen ? '' : ': ' + summary) + '</div>';
    if (usesOpen && st.uses.length) {
      h += '<table>';
      for (const u of hidden.concat(named)) h += useRow(u);
      if (vocab.length) {
        h += '<tr class="vhead"><td colspan="2" id="vhead">' + (vocabOpen ? '▾' : '▸') + ' vocabulary (' + vocab.length + ')</td></tr>';
        if (vocabOpen) for (const u of vocab) h += useRow(u);
      }
      h += '</table>';
    }
    return h;
  }

  function explodeHtml(st) {
    const W = cols(), ex = st.explode;
    const row = xrows[xsel];
    const text = (r) => src.slice(r.s, r.e).replace(/\s+/g, ' ').trim();
    const parts = [];
    parts.push('<span class="gnote">' + escapeHtml(text({ s: st.s, e: st.e })) + '</span>');
    parts.push(ex.ok ? '<span class="xok">✓ piecewise run reaches the same goals</span>'
      : '<span class="xerr">✗ ' + escapeHtml(ex.reason === 'backtracking' ? 'backtracking: the piecewise run reaches different goals' : (ex.reason || 'differs')) + '</span>');
    parts.push('');
    xrows.forEach((r, i) => {
      const ord = r.ordinal ? '(' + r.ordinal[0] + '/' + r.ordinal[1] + ') ' : '';
      const after = r.error ? '  ✗ error' : r.goals ? '  → ' + r.goals.fg.length + ' goal' + (r.goals.fg.length === 1 ? '' : 's') : '  (not run)';
      parts.push('<span class="xrow' + (i === xsel ? ' cur' : '') + '" data-x="' + i + '">' + ' '.repeat(r.depth * 2 + 2) + ord + escapeHtml(text(r)) + '<span class="gnote">' + after + '</span></span>');
    });
    parts.push('');
    const label = ' after ' + text(row) + ' ';
    parts.push('<span class="sep">' + '┄┄' + escapeHtml(label) + '┄'.repeat(Math.max(0, W - label.length - 2)) + '</span>');
    if (row.error) parts.push('<span class="gerr">' + escapeHtml(linesToText(layout(PP[row.error], W))) + '</span>');
    else if (row.goals) parts.push(goalsHtml({ status: 'ok', goals: row.goals }, { goals: row.prev }));
    else parts.push('<span class="gnote">(not run)</span>');
    return parts.join('\n');
  }

  /* --- gloss pane --- */
  let glossShown;   // what the pane holds, so stepping inside an item keeps its scroll
  function linkOf(full) {
    const r = resolveName(full);
    return r ? r.href : null;
  }
  function nameHtml(full, base, cls) {
    const href = linkOf(full);
    const inner = escapeHtml(base);
    return href ? '<a class="' + cls + '" href="' + escapeHtml(href) + '" data-full="' + escapeHtml(full) + '">' + inner + '</a>'
      : '<span class="' + cls + '" data-full="' + escapeHtml(full) + '">' + inner + '</span>';
  }
  const STATUS_NOTE = {
    'pending': 'not described yet',
    'stale:statement': 'the statement changed since this was written',
    'stale:type': 'the type prints differently since this was written',
    'stale:goals': 'the goals changed since this was written',
    'stale:uses': 'what the proof uses changed since this was written',
  };
  // A prose piece of the gloss: {text, status, was?, issue?} (or a bare string).
  const txt = (p) => typeof p === 'string' ? p : p && p.text ? p.text : '';
  const DG = G && G.diagrams ? G.diagrams : null;
  const prose = (t) => renderProse(t, resolveName, DG);
  const pendingHtml = (p, what) =>
    '<p>' + (p && p.issue ? escapeHtml(p.issue) : what + ' not described yet')
    + (p && p.was ? '<span class="was">' + renderProse(p.was, resolveName) + '</span>' : '') + '</p>';
  function itemHtml(it) {
    let h = '<h3>' + nameHtml(it.name, it.base, 'gname') + ' <span class="gkind">' + escapeHtml(kindLabel(it.kind)) + '</span></h3>';
    const hasProse = txt(it.long) || txt(it.commentary) || (it.proof || []).some(sg => txt(sg));
    const note = STATUS_NOTE[it.status];
    if (note && (txt(it.short) || hasProse)) h += '<div class="gstatus">' + note + '</div>';
    else if (hasProse && !it.reviewed) h += '<div class="gstatus">generated, not yet reviewed</div>';
    // The short line steps back (like an abstract) only before a long
    // that says the same at length; otherwise it is the item's reading.
    if (txt(it.short)) h += '<p class="gshort' + (txt(it.long) ? ' gabstract' : '') + '">'
      + renderProse(txt(it.short), resolveName).slice(3, -4) + '</p>';
    if (it.members && it.members.length) {
      h += '<table class="members">';
      for (const m of it.members)
        h += '<tr><td>' + nameHtml(m.name, m.base, 'mname') + '</td><td class="mshort">' + (txt(m.short) ? renderProse(txt(m.short), resolveName).slice(3, -4) : '') + '</td></tr>';
      h += '</table>';
    }
    if (it.body && txt(it.commentary)) {
      h += '<div class="gcomment">' + prose(txt(it.commentary)) + '</div>';
    } else if (it.body && it.commentary && it.commentary.status === 'pending' && (it.commentary.was || it.commentary.issue)) {
      h += '<div class="gstatus">' + pendingHtml(it.commentary, 'the commentary is') + '</div>';
    }
    if (it.body && Array.isArray(it.proof) && it.proof.length) {
      h += '<div class="gproof">Proof.</div>';
      for (const seg of it.proof) {
        const pending = seg.status === 'pending' || !txt(seg);
        h += '<div class="seg' + (pending ? ' pending' : '') + '" data-from="' + seg.from + '" data-to="' + seg.to + '" data-at="' + (it.body[0] + seg.from) + '">';
        h += pending ? pendingHtml(seg, 'steps ' + seg.from + (seg.to > seg.from ? '–' + seg.to : '')) : prose(txt(seg));
        h += '</div>';
      }
    } else if (it.body) {
      h += '<div class="gstatus">This proof has no description yet.</div>';
    } else if (txt(it.long)) {
      h += prose(txt(it.long));
    } else if (it.long && it.long.status === 'pending' && (it.long.was || it.long.issue)) {
      h += '<div class="gstatus">' + pendingHtml(it.long, 'this definition is') + '</div>';
    } else {
      h += '<div class="gstatus">No description yet.</div>';
    }
    // Diagrams harvested from the paper, until the prose places them.
    for (const dg of it.diagrams || []) {
      h += prose('```tikzcd' + (dg.opts || '') + '\n' + (dg.tikz || '') + '\n```')
        + '<div class="gfrom">the author\'s diagram</div>';
    }
    return h;
  }
  function summaryHtml() {
    let h = '<div class="gfile">' + escapeHtml(data.meta.file) + '</div>';
    if (G && G.short) h += '<p class="gshort">' + escapeHtml(G.short) + '</p>';
    if (G && G.summary) h += prose(G.summary);
    else if (G) h += '<div class="gstatus">No summary of this file yet.</div>';
    else h += '<div class="gstatus">No gloss for this file.</div>';
    return h;
  }
  function renderGloss() {
    if (!glossOpen) return;
    const it = G && cur >= 0 ? glossItemAt(G.items, cur) : null;
    const key = it ? it.name : '';
    if (key !== glossShown) {
      glossEl.innerHTML = it ? itemHtml(it) : summaryHtml();
      glossShown = key;
      if (!it) glossEl.parentElement.scrollTop = 0;
    }
    let curSeg = null;
    const pos = it && it.body && cur >= it.body[0] ? cur - it.body[0] : -1;
    glossEl.querySelectorAll('.seg').forEach(el => {
      const on = pos >= 0 && +el.dataset.from <= pos && pos <= +el.dataset.to;
      el.classList.toggle('cur', on);
      if (on) curSeg = el;
    });
    if (curSeg) curSeg.scrollIntoView({ block: 'nearest' });
    else if (it && cur === it.start) glossEl.parentElement.scrollTop = 0;
  }
  function toggleGloss() {
    glossOpen = !glossOpen;
    try { localStorage.setItem('glossOpen', glossOpen ? '1' : '0'); } catch (e) {}
    document.body.classList.toggle('gloss', glossOpen);
    glossShown = undefined;
    measure();
    renderGoals();
  }
  glossEl.addEventListener('click', (ev) => {
    if (ev.target.closest('a')) return;
    const el = ev.target.closest('.seg');
    if (el) setCur(+el.dataset.at, true);
  });

  /* --- constant popover: name, kind, short line, About --- */
  const popEl = document.getElementById('pop');
  const slices = new Map();   // slice URL -> Promise of its table (or null)
  const own = data.constants || null;
  function sliceOf(full) {
    const dir = full.slice(0, full.lastIndexOf('.'));
    if (!root) return null;
    const p = (lib && full.startsWith(lib + '.')) ? data.meta.page : pageOfLib(dir);
    return p ? root + '/constants/' + p.replace(/\.html$/, '.json') : null;
  }
  function loadSlice(url) {
    if (!slices.has(url))
      slices.set(url, fetch(url).then(r => r.ok ? r.json() : null).catch(() => null));
    return slices.get(url);
  }
  async function lookup(full) {
    if (own && own[full]) return own[full];
    const url = sliceOf(full);
    if (!url) return undefined;
    const t = await loadSlice(url);
    return t ? (t[full] || null) : undefined;
  }
  let popTimer = null, popFor = null, popAnchor = null;
  function hidePop() { popEl.hidden = true; popFor = null; popAnchor = null; }
  function placePop(anchor) {
    const r = anchor.getBoundingClientRect();
    popEl.style.left = '0px'; popEl.style.top = '0px';
    const w = popEl.offsetWidth, h = popEl.offsetHeight;
    let x = Math.min(r.left, window.innerWidth - w - 8), y = r.bottom + 4;
    if (y + h > window.innerHeight - 8) y = Math.max(8, r.top - h - 4);
    popEl.style.left = Math.max(8, x) + 'px';
    popEl.style.top = y + 'px';
  }
  const mods = data.mods || {};
  function showModPop(anchor) {
    const name = anchor.dataset.mod, m = mods[name] || {};
    const base = name.split('.').slice(-2).join('.');
    let h = '<div class="pname">' + (m.page ? '<a href="' + escapeHtml(m.page) + '">' + escapeHtml(base) + '</a>' : escapeHtml(base))
      + '<span class="pkind">module ' + escapeHtml(name.split('.').slice(0, -2).join('.')) + '</span></div>';
    if (m.short) h += '<div class="pshort">' + escapeHtml(m.short) + '</div>';
    if (m.summary) h += '<div class="psum">' + renderProse(m.summary, resolveName) + '</div>';
    else if (!m.short) h += '<div class="pnote">' + (m.page ? 'no description yet' : 'not built on this site') + '</div>';
    popEl.innerHTML = h;
    popEl.hidden = false;
    popFor = 'mod:' + name;
    placePop(anchor);
  }
  async function showPop(anchor) {
    if (anchor.dataset.mod) return showModPop(anchor);
    const full = anchor.dataset.full;
    const row = await lookup(full);
    if (popAnchor !== anchor) return;   // the pointer moved on
    const base = full.split('.').pop(), dir = full.slice(0, full.lastIndexOf('.'));
    const href = anchor.tagName === 'A' ? anchor.getAttribute('href') : linkOf(full);
    let h = '<div class="pname">' + (href ? '<a href="' + escapeHtml(href) + '">' + escapeHtml(base) + '</a>' : escapeHtml(base))
      + '<span class="pkind">' + escapeHtml(row && row.kind ? kindLabel(row.kind) : '') + ' ' + escapeHtml(dir) + '</span></div>';
    if (row && row.short) h += '<div class="pshort">' + renderProse(txt(row.short), resolveName).slice(3, -4) + '</div>';
    if (row && row.about) h += '<pre>' + docLinesHtml(row.about, 62, 0, 'about') + '</pre>';
    else if (row === undefined) h += '<div class="pnote">' + (root ? 'constants table not reachable' : 'no constants table in a single-page build') + '</div>';
    else if (row === null) h += '<div class="pnote">not in the constants table</div>';
    popEl.innerHTML = h;
    popEl.hidden = false;
    popFor = full;
    placePop(anchor);
  }
  document.addEventListener('mouseover', (ev) => {
    const a = ev.target.closest('[data-full], [data-mod]');
    clearTimeout(popTimer);
    if (a) {
      popAnchor = a;
      const key = a.dataset.mod ? 'mod:' + a.dataset.mod : a.dataset.full;
      if (popFor === key && !popEl.hidden) { placePop(a); return; }
      popTimer = setTimeout(() => showPop(a), 350);
    } else if (!ev.target.closest('#pop')) {
      popTimer = setTimeout(hidePop, 250);
    }
  });
  document.addEventListener('mouseout', (ev) => {
    const a = ev.target.closest('[data-full], [data-mod]');
    if (a && popAnchor === a && !ev.relatedTarget?.closest?.('#pop')) {
      clearTimeout(popTimer);
      popTimer = setTimeout(() => { if (popAnchor === a) { popAnchor = null; hidePop(); } }, 250);
    }
  });
  popEl.addEventListener('mouseleave', () => { popTimer = setTimeout(hidePop, 250); });
  popEl.addEventListener('mouseenter', () => clearTimeout(popTimer));
  document.addEventListener('scroll', hidePop, true);

  function markPiece() {
    if (cur < 0) return;
    const sent = srcEl.querySelector('.sent[data-i="' + cur + '"]');
    if (!sent) return;
    const row = xrows ? xrows[xsel] : null;
    sent.querySelectorAll('.pc').forEach(el => {
      el.classList.toggle('piece-cur', !!row && +el.dataset.s >= row.s && +el.dataset.e <= row.e);
    });
  }

  function renderGoals() {
    if (cur < 0) {
      goalPre.innerHTML = '<span class="gnote">(start of file — press ↓)</span>';
      usesEl.innerHTML = ''; msgEl.innerHTML = '';
      hintEl.textContent = '↓↑ step · h hyps' + (G ? ' · g gloss' : '');
      renderGloss();
      return;
    }
    const st = S[cur];
    if (xrows) {
      goalPre.innerHTML = explodeHtml(st);
      usesEl.innerHTML = ''; msgEl.innerHTML = '';
      hintEl.textContent = '↓↑ piece · x/esc back';
    } else {
      goalPre.innerHTML = goalsHtml(st, cur > 0 ? S[cur - 1] : null);
      usesEl.innerHTML = usesHtml(st);
      fillUseDescriptions();
      msgEl.innerHTML = messagesHtml(st);
      hintEl.textContent = '↓↑ step · h hyps' + (st.uses ? ' · u uses' + (usesOpen ? ' · v vocabulary' : '') : '') + (st.explode && st.explode.tree ? ' · x explode' : '') + (G ? ' · g gloss' : '');
    }
    markPiece();
    renderGloss();
  }

  function enterExplode() {
    const st = cur >= 0 ? S[cur] : null;
    if (!st || !st.explode || !st.explode.tree) return;
    xrows = flattenExplode(st.explode.tree, cur > 0 ? S[cur - 1].goals : null);
    xsel = 0;
    renderGoals();
  }
  function leaveExplode() { xrows = null; renderGoals(); }

  /* --- navigation --- */
  function setCur(i, scroll) {
    i = Math.max(-1, Math.min(S.length - 1, i));
    if (i === cur && scroll !== 'force') return;
    cur = i;
    xrows = null;
    const sents = srcEl.querySelectorAll('.sent');
    sents.forEach((el, k) => {
      el.classList.toggle('done', k < cur);
      el.classList.toggle('cur', k === cur);
    });
    if (cur >= 0) {
      const st = S[cur];
      posEl.textContent = (cur + 1) + ' / ' + S.length;
      kindEl.textContent = st.kind;
      msEl.textContent = st.ms + ' ms';
      if (scroll) sents[cur].scrollIntoView({ block: 'nearest' });
      try { history.replaceState(null, '', '#' + cur); } catch (e) { /* sandboxed frame */ }
    } else {
      posEl.textContent = '0 / ' + S.length;
      kindEl.textContent = ''; msEl.textContent = '';
      try { history.replaceState(null, '', location.pathname + location.search); } catch (e) { /* sandboxed frame */ }
    }
    renderGoals();
  }

  document.addEventListener('keydown', (ev) => {
    if (ev.altKey || ev.ctrlKey || ev.metaKey) return;
    if (xrows) {
      switch (ev.key) {
        case 'ArrowDown': case 'j': xsel = Math.min(xrows.length - 1, xsel + 1); renderGoals(); break;
        case 'ArrowUp': case 'k': xsel = Math.max(0, xsel - 1); renderGoals(); break;
        case 'Home': xsel = 0; renderGoals(); break;
        case 'End': xsel = xrows.length - 1; renderGoals(); break;
        case 'x': case 'Escape': leaveExplode(); break;
        case 'h': allHyps = !allHyps; renderGoals(); break;
        default: return;
      }
      ev.preventDefault();
      return;
    }
    switch (ev.key) {
      case 'ArrowDown': case 'j': setCur(cur + 1, true); break;
      case 'ArrowUp': case 'k': setCur(cur - 1, true); break;
      case 'x': enterExplode(); break;
      case 'u':
        usesOpen = !usesOpen;
        try { localStorage.setItem('usesOpen', usesOpen ? '1' : '0'); } catch (e) {}
        renderGoals(); break;
      case 'v':
        vocabOpen = !vocabOpen;
        try { localStorage.setItem('vocabOpen', vocabOpen ? '1' : '0'); } catch (e) {}
        renderGoals(); break;
      case 'PageDown': setCur(cur + 10, true); break;
      case 'PageUp': setCur(cur - 10, true); break;
      case 'Home': setCur(-1, true); break;
      case 'End': setCur(S.length - 1, true); break;
      case 'h': allHyps = !allHyps; renderGoals(); break;
      case 'g': toggleGloss(); break;
      case 'Escape': if (!popEl.hidden) hidePop(); else return; break;
      default: return;
    }
    ev.preventDefault();
  });
  srcEl.addEventListener('click', (ev) => {
    if (ev.target.closest('a')) return;
    const el = ev.target.closest('.sent');
    if (el) setCur(+el.dataset.i, false);
  });
  goalPre.addEventListener('click', (ev) => {
    const el = ev.target.closest('.xrow');
    if (el && xrows) { xsel = +el.dataset.x; renderGoals(); }
  });
  usesEl.addEventListener('click', (ev) => {
    if (ev.target.closest('a')) return;
    if (ev.target.closest('#vhead')) {
      vocabOpen = !vocabOpen;
      try { localStorage.setItem('vocabOpen', vocabOpen ? '1' : '0'); } catch (e) {}
      renderGoals();
      return;
    }
    if (ev.target.closest('#uhead')) {
      usesOpen = !usesOpen;
      try { localStorage.setItem('usesOpen', usesOpen ? '1' : '0'); } catch (e) {}
      renderGoals();
    }
  });
  let resizeTimer = null;
  window.addEventListener('resize', () => {
    clearTimeout(resizeTimer);
    resizeTimer = setTimeout(() => { measure(); renderGoals(); }, 100);
  });

  /* --- resizable panes: drag a divider, double-click to reset --- */
  const mainEl = document.querySelector('main'), rightEl = document.getElementById('right');
  const splits = [
    { el: document.getElementById('vsplit'), pane: document.getElementById('source'), box: mainEl, axis: 'x', key: 'splitV' },
    { el: document.getElementById('hsplit'), pane: document.getElementById('gloss'), box: rightEl, axis: 'y', key: 'splitH', fromEnd: true },
  ];
  for (const sp of splits) {
    try { const v = localStorage.getItem(sp.key); if (v) sp.pane.style.flexBasis = v; } catch (e) {}
    let raf = null;
    sp.el.addEventListener('pointerdown', (ev) => {
      ev.preventDefault();
      sp.el.setPointerCapture(ev.pointerId);
      sp.el.classList.add('dragging'); document.body.classList.add('dragging');
      document.body.style.cursor = sp.axis === 'x' ? 'col-resize' : 'row-resize';
      const move = (e) => {
        const r = sp.box.getBoundingClientRect();
        let frac = sp.axis === 'x' ? (e.clientX - r.left) / r.width : (e.clientY - r.top) / r.height;
        if (sp.fromEnd) frac = 1 - frac;
        frac = Math.max(0.15, Math.min(0.85, frac));
        sp.pane.style.flexBasis = (frac * 100).toFixed(1) + '%';
        if (!raf) raf = requestAnimationFrame(() => { raf = null; measure(); renderGoals(); });
      };
      const up = () => {
        sp.el.removeEventListener('pointermove', move);
        sp.el.removeEventListener('pointerup', up);
        sp.el.removeEventListener('pointercancel', up);
        sp.el.classList.remove('dragging'); document.body.classList.remove('dragging');
        document.body.style.cursor = '';
        try { localStorage.setItem(sp.key, sp.pane.style.flexBasis); } catch (e) {}
        measure(); renderGoals();
      };
      sp.el.addEventListener('pointermove', move);
      sp.el.addEventListener('pointerup', up);
      sp.el.addEventListener('pointercancel', up);
    });
    sp.el.addEventListener('dblclick', () => {
      sp.pane.style.flexBasis = '';
      try { localStorage.removeItem(sp.key); } catch (e) {}
      measure(); renderGoals();
    });
  }

  buildSource();
  measure();
  // #<n> is a sentence index; #def-<name> opens at the sentence that
  // defines <name> (what the paper's \formal marks link to).
  let start = -1;
  const m = /^#(\d+)$/.exec(location.hash);
  const md = /^#def-(.+)$/.exec(location.hash);
  if (m) start = +m[1];
  else if (md) {
    const name = decodeURIComponent(md[1]);
    const d = data.defs.find(d => d.name === name);
    if (d) start = S.findIndex(st => st.s <= d.s && d.s < st.e);
  }
  setCur(start, 'force');
}

if (typeof document !== 'undefined' && document.getElementById('data')) {
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', main);
  else main();
}
root.stepper = { layout, linesToText, tokenize, flat, width, flattenExplode, glossItemAt, renderProse, diagramKey };
if (typeof module !== 'undefined' && module.exports) module.exports = root.stepper;
})(typeof globalThis !== 'undefined' ? globalThis : this);
