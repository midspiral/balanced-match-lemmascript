# balanced-match — Verified with LemmaScript

This is a fork of [juliangruber/balanced-match](https://github.com/juliangruber/balanced-match) — a ~70-line, dependency-free utility used by 1B+ npm downloads/month (a transitive dep of `npm`, `webpack`, and most of the modern JS tooling stack) — with the algorithmic core, `range`, formally verified using [LemmaScript](https://github.com/midspiral/LemmaScript) (Dafny backend). The annotations sit **in-place** on the existing TypeScript source; no production-code refactoring.

`range(a, b, str)` is the stack-based balanced-bracket finder under the public `balanced(a, b, str)` API. Given delimiters like `{` and `}`, it walks `str` left-to-right, pushing every `a`-occurrence onto a stack, popping when it sees a matching `b`, and returns the start/end indices of the first balanced pair to fully close (or, as a fallback when nothing fully closes, the deepest inner pair that did). The algorithm is short but subtle — three branches mutating four interlocking variables, with an early-exit for the degenerate `a === b` case.

## Verified properties

For any inputs `a`, `b` with `a.length > 0 && b.length > 0`:

| Property | Statement |
|---|---|
| **Termination** | The main loop terminates for every input. Metric: `(result undefined ? 1 : 0) + (ai >= 0 ? |str| − ai : 0) + (bi >= 0 ? |str| − bi : 0)` — strictly decreases each iteration because branch 1 advances `ai`, branch 3 advances `bi`, branch 2 transitions `result` from undefined to a pair. |
| **Shape** | When `result !== undefined`, `result.length === 2`. |
| **Endpoint bounds** | `result[0] >= 0 && result[0] + a.length <= str.length` (and same for `result[1]` / `b`) — both endpoints are in-bounds for slicing. |
| **`a` is at `result[0]`** | `str.slice(result[0], result[0] + a.length) === a` — the first index is a valid `a`-occurrence position. |
| **`b` is at `result[1]`** | `str.slice(result[1], result[1] + b.length) === b` — the second index is a valid `b`-occurrence position. |
| **Ordering** | `result[0] <= result[1]` — the `a`-index is at or before the `b`-index. |

5 Dafny verification chunks, 0 errors. The TS annotations carry the contract (`requires`/`ensures` on `range`, plus loop invariants and the decreases metric); the `.dfy` file adds the proof-only invariants and assertions that LS's `\result`-narrowing doesn't reach (the `match result { case Some(v) => ... }` form for local-variable Option fields).

The ordering postcondition is supported by an `i == -1 || forall j, begs[j] <= i` invariant — every pushed entry is at or before the current scan position, with a disjunct for the terminal state where the loop is about to exit with leftover entries.

## What the proof attempt surfaced

Trying to strengthen the ordering to **strict** `result[0] < result[1]` failed — and constructing the counterexample took a single trace:

```
range("ab", "a", "aab")  ===>  [1, 1]
```

Walking through: position 1 of `"aab"` matches both `a = "ab"` (since `str[1..3] == "ab"`) and `b = "a"` (since `str[1..2] == "a"`). The algorithm pushes position 1 as an `a`-occurrence, later pops it via the fallback path, and sets both `left := 1` and `right := 1`. The returned `[left, right]` collapses to `[1, 1]`.

This isn't a bug in the algorithm — it's a real edge of the contract. Strict ordering would require a precondition that `a` and `b` don't co-locate any starting positions in `str`, which is non-trivial to state. The `<=` form holds universally.

## What's not (yet) verified (Phase 2)

- **Strict non-overlap** `result[0] + a.length <= result[1]` — does NOT hold in general. Even simpler counterexample than above: `a = "ab"`, `b = "b"`, `str = "ab"` → returns `[0, 1]` with `0 + 2 > 1`. The algorithm allows the `b`-substring to start inside the `a`-substring. Capturing exactly when non-overlap holds would split the postcondition by a "no shared starts" precondition on `(a, b, str)`.
- **Dyck-balanced body** — when the returned pair *is* non-overlapping, the substring between `result[0] + a.length` and `result[1]` should be balanced: equal counts of non-overlapping `a` and `b` occurrences with every prefix having `count(a) ≥ count(b)`. This is the headline correctness property (no bracket mismatch hides between the matched pair) and requires a ghost model of the stack tied to substring-occurrence counts.
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

Six small, broadly-useful extensions:

1. **`Array.pop()` lowering** — `let x = arr.pop()` desugars to a two-statement form: `var x: T? = (if |arr| > 0 then Some(arr[|arr|-1]) else None); arr := (if |arr| > 0 then arr[..|arr|-1] else arr);`. Mirrors the existing `Array.shift()` lowering. Handles both `let` and `assign` positions; receiver must be a `var`. Helper factored as `buildPopLowering`.
2. **Type-driven defaults for uninitialized `let`** — `let x: T[];` → `[]`, `let x: T | undefined;` → `None`, `let x: number;` → `0`, etc. The previous "emit `default` and let Dafny complain" path was always wrong; this fix is generic across case studies. Also extended the optional-detection regex to handle leading `undefined | T` / `null | T` (was only catching trailing).
3. **`StringIndexOfFrom` accepts `int`** — was `nat`, which forced callers to discharge `from >= 0` for `str.indexOf(s, fromIdx)` calls where `fromIdx` was an int. Now clamps internally (matching TS's behavior of treating negative `fromIdx` as 0). Plus added `ensures` clauses on all three `StringIndexOf*` helpers (relating result to `from`, validating the match substring) — these are what makes downstream proofs about indexOf results tractable.
4. **`indexOf(s, from)` emits with both args** — pre-fix, the dafny-emit silently dropped the second argument, silently turning `str.indexOf(b, ai + 1)` into `StringIndexOf(str, b)` (searching from 0 — wrong semantics).
5. **`&&` narrowing on either conjunct** — `if (begs.length && right !== undefined)` now narrows `right` to its unwrapped value in the body. Previously LS only recognized the optional check as the *leftmost* conjunct; this fix walks the `&&` tree and accepts the check on either side.
6. **Truthy coercion on `int`/`array` conditions** — `if (n)`, `while (n)`, `n ? a : b` where `n: number` (or `xs: T[]`) now coerce to `n > 0` / `|xs| > 0`. The conditional case used to handle `string` only.
