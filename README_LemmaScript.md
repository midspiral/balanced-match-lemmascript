# balanced-match — Verified with LemmaScript

This is a fork of [juliangruber/balanced-match](https://github.com/juliangruber/balanced-match) — a ~70-line, dependency-free utility used by 1B+ npm downloads/month (a transitive dep of `npm`, `webpack`, and most of the modern JS tooling stack) — with the algorithmic core, `range`, formally verified using [LemmaScript](https://github.com/midspiral/LemmaScript) (Dafny backend). The annotations sit **in-place** on the existing TypeScript source; no production-code refactoring.

`range(a, b, str)` is the stack-based balanced-bracket finder under the public `balanced(a, b, str)` API. Given delimiters like `{` and `}`, it walks `str` left-to-right, pushing every `a`-occurrence onto a stack, popping when it sees a matching `b`, and returns the start/end indices of the first balanced pair to fully close (or, as a fallback when nothing fully closes, the deepest inner pair that did). The algorithm is short but subtle — three branches mutating four interlocking variables, with an early-exit for the degenerate `a === b` case.

## Verified properties (Phase 1)

For any inputs `a`, `b` with `a.length > 0 && b.length > 0`:

| Property | Statement |
|---|---|
| **Termination** | The main loop terminates for every input. Metric: `(result undefined ? 1 : 0) + (ai >= 0 ? |str| − ai : 0) + (bi >= 0 ? |str| − bi : 0)` — strictly decreases each iteration because branch 1 advances `ai`, branch 3 advances `bi`, branch 2 transitions `result` from undefined to a pair. |
| **Shape** | When `result !== undefined`, `result.length === 2`. |
| **Endpoint bounds** | `result[0] >= 0 && result[0] + a.length <= str.length` (and same for `result[1]` / `b`) — both endpoints are in-bounds for slicing. |
| **`a` is at `result[0]`** | `str.slice(result[0], result[0] + a.length) === a` — the first index is a valid `a`-occurrence position. |
| **`b` is at `result[1]`** | `str.slice(result[1], result[1] + b.length) === b` — the second index is a valid `b`-occurrence position. |

5 Dafny obligations verified, 0 errors. The TS annotations carry the contract (`requires`/`ensures` on `range`, plus loop invariants and decreases metric); the `.dfy` file adds the proof-only invariants and assertions that LS's `\result`-narrowing doesn't reach (the `match result { case Some(v) => ... }` form for local-variable Option fields).

## What's not (yet) verified (Phase 2)

- **Ordering**: `result[0] <= result[1]` — when `a !== b`, the algorithm finds non-overlapping pairs, so the tighter `result[0] + a.length <= result[1]` holds. (The `a === b` early-return *does* allow overlap: e.g. `range("aa", "aa", "aaa")` returns `[0, 1]` with overlap.) Phase 2 will split the postcondition by `a === b`.
- **Dyck-balanced body** — the substring between `result[0] + a.length` and `result[1]` should have equal counts of non-overlapping `a` and `b` occurrences, with every prefix having `count(a) ≥ count(b)`. This is the headline correctness property (no bracket mismatch hides between the matched pair) and requires a ghost model of the stack.
- **First-balanced-pair-to-close** — the algorithm has a particular canonical choice; characterizing it precisely would tighten what callers can rely on.
- **Fallback path** — when the loop exits with non-empty `begs` and `right !== undefined`, the returned pair `[left, right]` is the deepest opened-and-closed inner pair. Phase 1 verifies its endpoint validity; Phase 2 would characterize which pair it is.

`balanced` itself (the regex-accepting wrapper) is out of scope per the project's no-regex rule.

## Setup

**Prerequisites:** [Dafny](https://github.com/dafny-lang/dafny) ≥ 4.x, Node.js ≥ 18, and the LemmaScript toolchain cloned next to this repo:

```sh
git clone https://github.com/midspiral/LemmaScript.git ../LemmaScript
cd ../LemmaScript && npm install && npm run build
```

## Verify

```sh
cd src
node ../../LemmaScript/tools/dist/lsc.js check --backend=dafny index.ts
```

Output:

```
Dafny program verifier finished with 5 verified, 0 errors
```

## File Structure

```
src/
  index.ts        ← Production TypeScript with //@ annotations on `range`
  index.dfy.gen   ← LS-generated Dafny (regeneratable from index.ts)
  index.dfy       ← Verification target: gen + proof-only invariants & asserts
```

The diff between `index.dfy.gen` and `index.dfy` is additions-only — all additions are loop invariants Dafny needs that can't be expressed in the TS surface (because LS's narrowing of `match` on local `Option`-typed vars doesn't reach into the invariant), plus a handful of asserts that bridge facts from invariants to use-sites.

## LemmaScript toolchain additions driven by this case study

Five small, broadly-useful extensions:

1. **`Array.pop()` lowering** — `let x = arr.pop()` desugars to a two-statement form: `var x: T? = (if |arr| > 0 then Some(arr[|arr|-1]) else None); arr := (if |arr| > 0 then arr[..|arr|-1] else arr);`. Mirrors the existing `Array.shift()` lowering. Handles both `let` and `assign` positions; receiver must be a `var`. Helper factored as `buildPopLowering`.
2. **Type-driven defaults for uninitialized `let`** — `let x: T[];` → `[]`, `let x: T | undefined;` → `None`, `let x: number;` → `0`, etc. The previous "emit `default` and let Dafny complain" path was always wrong; this fix is generic across case studies. Also extended the optional-detection regex to handle leading `undefined | T` / `null | T` (was only catching trailing).
3. **`StringIndexOfFrom` accepts `int`** — was `nat`, which forced callers to discharge `from >= 0` for `str.indexOf(s, fromIdx)` calls where `fromIdx` was an int. Now clamps internally (matching TS's behavior of treating negative `fromIdx` as 0). Plus added `ensures` clauses on all three `StringIndexOf*` helpers (relating result to `from`, validating the match substring) — these are what makes downstream proofs about indexOf results tractable.
4. **`indexOf(s, from)` emits with both args** — pre-fix, the dafny-emit silently dropped the second argument, silently turning `str.indexOf(b, ai + 1)` into `StringIndexOf(str, b)` (searching from 0 — wrong semantics).
5. **`&&` narrowing on either conjunct** — `if (begs.length && right !== undefined)` now narrows `right` to its unwrapped value in the body. Previously LS only recognized the optional check as the *leftmost* conjunct; this fix walks the `&&` tree and accepts the check on either side.
6. **Truthy coercion on `int`/`array` conditions** — `if (n)`, `while (n)`, `n ? a : b` where `n: number` (or `xs: T[]`) now coerce to `n > 0` / `|xs| > 0`. The conditional case used to handle `string` only.

(Plus `extractLeftmostOptionalCheck` being extended to walk into `&&` on either side; that's part of #5.)
