# balanced-match — Verified with LemmaScript

This is a fork of [juliangruber/balanced-match](https://github.com/juliangruber/balanced-match) — a ~70-line, dependency-free utility used by 1B+ npm downloads/month (a transitive dep of `npm`, `webpack`, and most of the modern JS tooling stack) — with the algorithmic core, `range`, formally verified using [LemmaScript](https://github.com/midspiral/LemmaScript) (Dafny backend). The annotations sit **in-place** on the existing TypeScript source; no production-code refactoring.

`range(a, b, str)` is the stack-based balanced-bracket finder under the public `balanced(a, b, str)` API. Given delimiters like `{` and `}`, it walks `str` left-to-right, pushing every `a`-occurrence onto a stack, popping when it sees a matching `b`, and returns the start/end indices of the first balanced pair to fully close (or, as a fallback when nothing fully closes, the deepest inner pair that did). The algorithm is short but subtle — three branches mutating four interlocking variables, with an early-exit for the degenerate `a === b` case.

## Verified properties

For any inputs `a`, `b` with `a.length > 0 && b.length > 0` (plus a `NoOverlap` precondition for the Dyck-balance invariant — see below):

| Property | Statement |
|---|---|
| **Termination** | The main loop terminates for every input. Metric: `(result undefined ? 1 : 0) + (ai >= 0 ? |str| − ai : 0) + (bi >= 0 ? |str| − bi : 0)` — strictly decreases each iteration because branch 1 advances `ai`, branch 3 advances `bi`, branch 2 transitions `result` from undefined to a pair. |
| **Shape** | When `result !== undefined`, `result.length === 2`. |
| **Endpoint bounds** | `result[0] >= 0 && result[0] + a.length <= str.length` (and same for `result[1]` / `b`) — both endpoints are in-bounds for slicing. |
| **`a` is at `result[0]`** | `str.slice(result[0], result[0] + a.length) === a` — the first index is a valid `a`-occurrence position. |
| **`b` is at `result[1]`** | `str.slice(result[1], result[1] + b.length) === b` — the second index is a valid `b`-occurrence position. |
| **Ordering** | `result[0] <= result[1]` — the `a`-index is at or before the `b`-index. |
| **Dyck-balance foundation (Phase 2)** | Under `NoOverlap` (no position of `str` is both an `a`-start and a `b`-start): `pushedCount == CountAll(str, a, begs[0], ai-bound)` and `poppedCount == CountAll(str, b, begs[0], bi-bound)` throughout the loop. The algorithm's per-branch push/pop counts equal the overlapping occurrence counts of `a` and `b` in the substring `str[begs[0]..]` up to the current scan position. |

The TS annotations carry the contract (`requires`/`ensures` on `range`, plus loop invariants and the decreases metric); the `.dfy` file adds the proof-only invariants, helper lemmas, and bridging asserts that LS's `\result`-narrowing doesn't reach.

## What the proof attempt surfaced

Trying to strengthen the ordering to **strict** `result[0] < result[1]` failed — and constructing the counterexample took a single trace:

```
range("ab", "a", "aab")  ===>  [1, 1]
```

Walking through: position 1 of `"aab"` matches both `a = "ab"` (since `str[1..3] == "ab"`) and `b = "a"` (since `str[1..2] == "a"`). The algorithm pushes position 1 as an `a`-occurrence, later pops it via the fallback path, and sets both `left := 1` and `right := 1`. The returned `[left, right]` collapses to `[1, 1]`.

This isn't a bug in the algorithm — it's a real edge of the contract. Strict ordering would require a precondition that `a` and `b` don't co-locate any starting positions in `str`, which is exactly the `NoOverlap` precondition the Phase 2 invariants depend on.

## Phase 2 proof structure

The Dyck-balance foundation invariants connect the algorithm's *event counts* (each branch-1 push, branch-2 / branch-3 pop) to *substring occurrence counts* in `str`. The proof rests on five pieces:

1. **`CountAll(s, sub, lo, hi)`** — a ghost function counting overlapping occurrences of `sub` in `s[lo..hi]`. Defined by recursion on `hi` so the recursive case *is* the extension-by-one equation; no separate extension lemma needed beyond what the body computes.
2. **`IndexOfMaxAt`** — a pointwise maximality lemma: at any position `p` strictly before `StringIndexOfFromN(s, sub, from)`, `sub` does not start at `p`. Avoids the quantifier-trigger trap of stating maximality as a forall in `StringIndexOf`'s postcondition.
3. **`CountAllExtendNoMatch` / `CountAllExtendOneMatch`** — extension lemmas: extending the upper bound over a range with no new matches (or exactly one) changes `CountAll` by 0 or 1.
4. **`CountAllExtendsByOne`** — the *single-forall* helper. Given that `s[p..p+|sub|] == sub` and `nextFrom = StringIndexOfFromN(s, sub, p+1)`, it bundles "build the no-match forall over `(matchK, hi_new]` using `IndexOfMaxAt`" and "apply `CountAllExtendOneMatch`" into one lemma. This is the key factoring — the `forall k` block lives in the lemma's body (small context), not in the main method.
5. **`CountAllZeroFromOtherStart` + `NoOverlapAtAPos`** — for the iter-1 case (first push), establishes `poppedCount == 0 == CountAll(str, b, begs[0], hi_b)` by combining a point-wise NoOverlap fact with `CountAllExtendNoMatch`.

Plus three ghost-state additions in the loop:

- **`pushedCount`/`poppedCount` ghost counters** — accounting `|begs| == pushedCount - poppedCount` (algorithmic foundation).
- **`aiLowerBound`/`biLowerBound` ghost trackers** — the `from` arguments most recently passed to `indexOf`. Combined with the invariant `bi == StringIndexOfFromN(str, b, biLowerBound)`, this lets the maintenance proofs apply `IndexOfMaxAt` at the right `from` without re-deriving it.
- **Loop-entry pin invariant** — `|begs| == 0 && result.None? ==> pushedCount == 0 && poppedCount == 0 && bounds at initial values`. Iter 1 is the only iteration with empty `begs` and `result` still `None`; this invariant lets the iter-1 maintenance proof transition cleanly from "vacuous" to "established."

**Verification cost.** Even with the lemma factoring, Z3 needs `--isolate-assertions` and a per-assertion timeout of ~200 seconds to discharge the iter-1 case (specifically, the `CountAllZeroFromOtherStart` maintenance for the poppedCount invariant). The case study is therefore registered in `LemmaScript-files.txt` with `300 --isolate-assertions`, which puts it on the `check.sh dafny-slow` track (not the default `dafny` track).

## What's not (yet) verified

- **Strict non-overlap** `result[0] + a.length <= result[1]` — does NOT hold in general. Counterexample: `a = "ab"`, `b = "b"`, `str = "ab"` → returns `[0, 1]` with `0 + 2 > 1`. The algorithm allows the `b`-substring to start inside the `a`-substring.
- **Dyck-balance as an `ensures`** — the count-balance is currently a loop invariant tied to ghost counters, not an `ensures` on the returned `[s, e]`. Converting it to an output property would require characterizing `pushedCount == poppedCount` at the moment `result` is set in branch 2 and deriving `CountAll(str, a, s+1, e) == CountAll(str, b, s+1, e)` from the invariants, plus handling the fallback path separately.
- **First-balanced-pair-to-close** — the algorithm has a particular canonical choice (the leftmost `a` whose matching `b` fully closes the run); characterizing this precisely would tighten what callers can rely on.
- **Fallback path semantics** — when the loop exits with non-empty `begs` and `right !== undefined`, the returned `[left, right]` is the deepest opened-and-closed inner pair. Endpoint validity is verified; *which* pair it is, isn't.

`balanced` itself (the regex-accepting wrapper) is out of scope per the project's no-regex rule.

## Setup

**Prerequisites:** [Dafny](https://github.com/dafny-lang/dafny) ≥ 4.x, Node.js ≥ 18, and the LemmaScript toolchain cloned next to this repo:

```sh
git clone https://github.com/midspiral/LemmaScript.git ../LemmaScript
cd ../LemmaScript && npm install && npm run build
```

## Verify

The Phase 2 invariants require Dafny's `--isolate-assertions` mode with a per-assertion time limit of ~200s — this is set up via `LemmaScript-files.txt` in the repo root:

```
src/index.ts 300 --isolate-assertions
```

Run via the LemmaScript `check.sh` driver in `dafny-slow` mode (which honors per-file timeouts above the default 60s CI ceiling):

```sh
../LemmaScript/tools/check.sh dafny-slow
```

Output:

```
Dafny program verifier finished with 424 verified, 0 errors
```

(The default `check.sh dafny` mode skips this file as gen-check-only because its timeout exceeds the 60s CI threshold.)

## File Structure

```
src/
  index.ts            ← Production TypeScript with //@ annotations on `range`
  index.dfy.gen       ← LS-generated Dafny (regeneratable from index.ts)
  index.dfy           ← Verification target: gen + proof-only lemmas, invariants, asserts
LemmaScript-files.txt ← Registers index.ts with the 300s --isolate-assertions config
```

The diff between `index.dfy.gen` and `index.dfy` is additions-only — proof-only lemmas (`CountAll`, `IndexOfMaxAt`, `CountAllExtend*`, `CountAllExtendsByOne`, `CountAllZeroFromOtherStart`, `NoOverlapAtAPos`), loop invariants Dafny needs that can't be expressed in the TS surface, plus bridging asserts that thread facts from invariants to use-sites.

## LemmaScript toolchain additions driven by this case study

Six small, broadly-useful extensions:

1. **`Array.pop()` lowering** — `let x = arr.pop()` desugars to a two-statement form: `var x: T? = (if |arr| > 0 then Some(arr[|arr|-1]) else None); arr := (if |arr| > 0 then arr[..|arr|-1] else arr);`. Mirrors the existing `Array.shift()` lowering. Handles both `let` and `assign` positions; receiver must be a `var`. Helper factored as `buildPopLowering`.
2. **Type-driven defaults for uninitialized `let`** — `let x: T[];` → `[]`, `let x: T | undefined;` → `None`, `let x: number;` → `0`, etc. The previous "emit `default` and let Dafny complain" path was always wrong; this fix is generic across case studies. Also extended the optional-detection regex to handle leading `undefined | T` / `null | T` (was only catching trailing).
3. **`StringIndexOfFrom` accepts `int`** — was `nat`, which forced callers to discharge `from >= 0` for `str.indexOf(s, fromIdx)` calls where `fromIdx` was an int. Now clamps internally (matching TS's behavior of treating negative `fromIdx` as 0). Plus added `ensures` clauses on all three `StringIndexOf*` helpers (relating result to `from`, validating the match substring) — these are what makes downstream proofs about indexOf results tractable.
4. **`indexOf(s, from)` emits with both args** — pre-fix, the dafny-emit silently dropped the second argument, silently turning `str.indexOf(b, ai + 1)` into `StringIndexOf(str, b)` (searching from 0 — wrong semantics).
5. **`&&` narrowing on either conjunct** — `if (begs.length && right !== undefined)` now narrows `right` to its unwrapped value in the body. Previously LS only recognized the optional check as the *leftmost* conjunct; this fix walks the `&&` tree and accepts the check on either side.
6. **Truthy coercion on `int`/`array` conditions** — `if (n)`, `while (n)`, `n ? a : b` where `n: number` (or `xs: T[]`) now coerce to `n > 0` / `|xs| > 0`. The conditional case used to handle `string` only.
