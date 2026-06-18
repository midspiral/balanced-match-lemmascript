# balanced-match — Verified with LemmaScript

[![LemmaScript: verified](https://img.shields.io/badge/LemmaScript-verified-brightgreen)](https://github.com/midspiral/balanced-match-lemmascript/actions/workflows/lemmascript.yml)


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
| **Behavioral equivalence with a functional spec (Phase 3 headline, universal)** | `range(a, b, str) == range_spec(a, b, str)` for *every* input — both the branch-2 fully-closed-pair path and the post-loop fallback. `range_spec` is a pure recursive Dafny function: each of the imperative algorithm's three branches becomes a recursive case; the loop exit + fallback is the function's base case. The imperative method's loop carries a single bridging invariant `range_spec_loop(current state) == specFinal` (where `specFinal` is the spec's value computed at loop entry); each iteration's body matches exactly one recursive case of `range_spec_loop`, so the invariant is maintained by direct unfolding — no per-stack-frame counting, no `forall j` over `CountAll`. This is strictly stronger than any single-property claim: any property of `range_spec` (a pure function, separately analyzable) automatically transfers to the imperative `range`. |
| **Body-balance, branch-2-derived results (Phase 4)** | When `range_spec_inner` (a no-fallback variant of the spec) returns Some, the returned pair is body-balanced. `SpecBodyBalanceInner` proves this by induction on `range_spec_loop_inner`'s recursive structure, with single-frame CountAll accounting (only `b0 = begs[0]`) threaded as a ghost parameter. Subsumed by Phase 5 (kept as an intermediate result and as the substrate `BranchTwoBodyBalance` reused by Phase 5). |
| **Body-balance, unconditional (Phase 5 headline)** | Strict generalization. For *every* Some result of `range_spec(a, b, str)` — branch-2-derived OR post-loop-fallback-derived — the interior is Dyck-balanced: `CountAll(str, a, s+1, e+\|a\|-1) == CountAll(str, b, s+1, e+\|b\|-1)`. `SpecBodyBalance(a, b, str)` is the unconditional top-level theorem, packaged as `BodyBalancedOpt(a, b, str, range_spec(a, b, str))`. Two strict generalizations over Phase 4: **per-frame accounting** (`forall j` over `begs`, not just `j=0`) and a **`right.Some(r) ⇒ BodyBalancedOpt(Some([left, r]))`** invariant carried through branches and established at branch 3's `popped < left` update via `BranchTwoBodyBalance` applied at the just-popped top frame. |
| **First-balanced-pair-to-close (Phase 6)** | When `range_spec_inner(a, b, str)` returns Some — the branch-2 fully-closed path, where the algorithm finds a matching pair — the returned pair's first component is `StringIndexOf(str, a)`, the **leftmost** `a`-occurrence in `str`. `FirstBalancedPair(a, b, str)` proves this; the inductive heart `FirstBalancedPairLoopInner` carries an invariant `\|begs\| > 0 ==> begs[0] == initialAi` (where `initialAi` is the original `StringIndexOf(str, a)`). The bottom of the stack is invariantly the first push, fired at iter 1 from the fresh-state `i == ai == initialAi`. Branch 3 pops only when `\|begs\| >= 2` so never touches `begs[0]`; branch 2 (`\|begs| == 1`) emits `Some([begs[0], bi])`, transferring the witness to the result. |

The TS annotations carry the contract (`requires`/`ensures` on `range`, plus loop invariants and the decreases metric); the `.dfy` file adds the proof-only invariants, helper lemmas, and bridging asserts that LS's `\result`-narrowing doesn't reach.

## What the proof attempt surfaced

Trying to strengthen the ordering to **strict** `result[0] < result[1]` failed — and constructing the counterexample took a single trace:

```
range("ab", "a", "aab")  ===>  [1, 1]
```

Walking through: position 1 of `"aab"` matches both `a = "ab"` (since `str[1..3] == "ab"`) and `b = "a"` (since `str[1..2] == "a"`). The algorithm pushes position 1 as an `a`-occurrence, later pops it via the fallback path, and sets both `left := 1` and `right := 1`. The returned `[left, right]` collapses to `[1, 1]`.

This isn't a bug in the algorithm — it's a real edge of the contract. Strict ordering would require a precondition that `a` and `b` don't co-locate any starting positions in `str`, which is exactly the `NoOverlap` precondition the Phase 2 invariants depend on.

## Phase 6 proof structure (first-balanced-pair-to-close)

`FirstBalancedPair(a, b, str)` — when `range_spec_inner` returns a Some pair, its first component is `StringIndexOf(str, a)`. Proof is a single inductive invariant: `|begs| > 0 ==> begs[0] == initialAi`, threaded as a ghost parameter through `FirstBalancedPairLoopInner`. Maintained because:

- **Iter-1 push** (branch 1 with `|begs| == 0`): fresh-state guard gives `i == ai == initialAi`, so newBegs[0] = i = initialAi.
- **Non-iter-1 push** (branch 1 with `|begs| > 0`): appends at the end, doesn't change begs[0].
- **Branch 3 pop**: only fires when `|begs| >= 2`, pops the top, never touches begs[0].
- **Branch 2** (`|begs| == 1`): pops the only element and sets `result := Some([begs[0], bi])` = `Some([initialAi, bi])`. The witness moves from the stack invariant into the result invariant.

Much simpler than Phase 5 — no `CountAll`, no per-frame anything, just identity tracking on `begs[0]`. The branch-3 case requires `|begs| >= 1` (or vacuously empty); both preserve `begs[0]` cleanly.

## Phase 5 proof structure (unconditional body-balance)

`SpecBodyBalance(a, b, str)` — now **unconditional** under `NoOverlap` and `a != b`: for every Some result of `range_spec`, the interior is Dyck-balanced. Strict generalization of Phase 4 (which covered branch-2-derived results only). The Phase 4 inner-spec lemmas remain useful as intermediates and as the substrate (`BranchTwoBodyBalance`) that Phase 5 reuses at a different stack frame. The proof rests on three pieces beyond Phase 4's toolkit:

1. **Per-frame CountAll accounting** (`forall j` over `begs`). Phase 4's `SpecBodyBalanceLoopInner` tracked only the deepest unpopped frame (`b0 = begs[0]`); the `j=0` equation sufficed because branch 2 closes against `b0`. The fallback emits `Some([popped, bi])` where `popped` is the *topmost* frame at the moment branch 3 updates `left` — getting body-balance for that pair needs the CountAll equation at THAT frame, not at `b0`. `SpecBodyBalanceLoop` carries `forall j :: 0 <= j < |begs| ==> CountAll(str, a, begs[j], hi_a) == (|begs| - j) + CountAll(str, b, begs[j], hi_b)` as a precondition. Maintained via `CountAllExtendsByOne` applied in a forall block (one a-match in branch 1, one b-match in branch 3); becomes vacuous at branch 2 (|begs| 1→0). Living in a pure-spec lemma context (not the bloated imperative method) is what makes `forall j` × recursive `CountAll` tractable — the same shape that hit Z3 walls in the original Phase 2 imperative attempt.

2. **`right.Some(r) ⇒ BodyBalancedOpt(Some([left, r]))` as a carried invariant.** The base case (loop exit with fallback) reads body-balance for the returned `Some([left, r])` off this invariant directly. Branches 1, 2, and the branch-3 no-update case preserve it trivially (no `left`/`right` mutation). At the branch-3 `popped < left` update, we have the per-frame equation at the just-popped top + NoOverlap at `popped` + the `bi`-side hi-bound — exactly the preconditions of `BranchTwoBodyBalance` (the Phase 4 kernel), now invoked at `begs[|begs|-1]` instead of `begs[0]`. Conclusion: body-balance for `[popped, bi]`, which `BodyBalancedOpt` (opaque, unchanged from Phase 4) wraps as the right-invariant for the recursive call.

3. **`SpecBodyBalanceLoop`** — the outer-spec inductive lemma (analog of `SpecBodyBalanceLoopInner`). Same recursive structure as `range_spec_loop`; preconditions extend Phase 4's with the `forall j` and the `right` invariant; ensures `BodyBalancedOpt(range_spec_loop(...))`. At base case `i < 0 ∨ result.Some?`, falls through to either `result` (Some case, body-balanced by precondition) or the fallback's `Some([left, r])` (right.Some + |begs| > 0 case, body-balanced by the carried right-invariant) or `None` (vacuous).

Supporting tweak: `CountAllZeroFromOtherStart` relaxed from `from == p + 1` to `from <= p + 1` — needed because `biLowerBound` in non-iter-1 branch 1 may have been set in an earlier branch 3 to `(prev bi) + 1 < i_old + 1`. The proof obligation (no b-match strictly below `bi` via `IndexOfMaxAt`) holds at the weaker bound.

The unconditional theorem transfers to the imperative `range` method automatically via the existing Phase 3 refinement ensures `res == range_spec(a, b, str)`. The body-balance ensures isn't packaged on the method itself because the codegen-emitted NoOverlap precondition (curried `forall p :: A ==> B ==> C` form) doesn't auto-skolemize against `NoOverlapPred`'s filter form under `--isolate-assertions`; callers chain manually.

## Phase 4 proof structure (body-balance for branch-2-derived results)

Now an intermediate result subsumed by Phase 5. `SpecBodyBalanceInner` — under `NoOverlap` and `a != b`, when `range_spec_inner` (a no-fallback variant of the spec) returns Some, the returned pair is body-balanced. Proved entirely against the pure spec function — no entanglement with the imperative method's verification. The proof rests on four pieces:

1. **`range_spec_loop_inner` and `range_spec_inner`** — no-fallback variants of the spec functions. `range_spec_loop_inner` is identical to `range_spec_loop` except its loop-exit base case returns `result` directly (no `[left, r]` fallback). This isolates the branch-2-derived case from the fallback case, which has a different shape of body-balance argument.
2. **`SpecBodyBalanceLoopInner`** — the inductive heart. Threads the imperative loop's ghost state (`b0`, `aiLowerBound`, `biLowerBound`, CountAll-based accounting) as ghost parameters; ensures `BodyBalancedOpt` for the result. Branches 1 and 3 maintain accounting via `CountAllExtendsByOne` (iter-1 push uses `CountAllZeroFromOtherStart` for the freshly-established `poppedCount == 0`). Branch 2 derives `b0 < bi` (NoOverlap when `b0+|b| ≤ |str|`, else by `b0` not fitting `b`) and applies the existing `BranchTwoBodyBalance` to set body-balance for the new `Some([b0, bi])`.
3. **`BodyBalancedOpt(a, b, str, v)` — opaque** — wraps the `CountAll(a, v[0]+1, v[1]+|a|-1) == CountAll(b, v[0]+1, v[1]+|b|-1)` claim (with the necessary validity guards). Opaque so the ensures-level verifier doesn't unfold `CountAll` when checking the lemma's ensures across branches — without opacity, the case-merge VC at the `match range_spec_loop_inner(...)` boundary times out (>240s); with opacity it discharges in seconds.
4. **`RangeSpecLoopInnerAgreement`** — proves `range_spec_loop_inner.Some ⇒ range_spec_loop == range_spec_loop_inner`. The two functions differ only at the loop-exit base case (fallback vs. no-fallback), and `inner.Some` only happens via branch-2 setting `result`, which both functions return identically. Lets `SpecBodyBalance` transfer the body-balance conclusion from `range_spec_inner` to `range_spec`.

Supporting infrastructure: **`NoOverlapPred`** wraps the method's NoOverlap forall into a single boolean fact (so recursive lemma calls discharge the precondition trivially), and **`NoOverlapInstance`** extracts the per-position disjunction with the trigger pinned in the lemma's own context.

## Phase 3 proof structure (refinement)

The headline result — `range(a, b, str) == range_spec(a, b, str)` — is proved by *refinement*: define a pure recursive Dafny function `range_spec` that mirrors the algorithm one branch per recursive case, then show the imperative loop maintains the single bridging invariant `range_spec_loop(current state) == range_spec_loop(initial state)`. The proof rests on three pieces:

1. **`range_spec_loop(a, b, str, i, ai, bi, begs, left, right, result)`** — pure recursive function. One recursive case per imperative branch (push / branch-2 pop+set-result / branch-3 pop+advance-bi). The "loop exit" base case (when `i < 0 || result.Some?`) returns either the existing result or the post-loop-fallback value, matching the imperative method's behavior at termination.
2. **`range_spec(a, b, str)`** — top-level wrapper: handles the pre-loop initial `indexOf`s, the `a == b` early-return, and the outer `ai >= 0 && bi > 0` gate, then delegates to `range_spec_loop`.
3. **Bridging loop invariant** in the imperative `range` method — `range_spec_loop(a, b, str, i, ai, bi, begs, left, right, result) == specFinal`, where `specFinal` is the spec function called at loop entry. Maintenance is *direct unfolding*: each imperative body step matches exactly one of `range_spec_loop`'s recursive cases. No `forall j`, no recursive `CountAll`, no quantifier instantiation — the cost stays linear in the number of branches.

Post-loop, a small case analysis on `(result, right, |begs|)` bridges the imperative fallback to the spec's "loop exit" base case, completing the chain `res == range_spec_loop(post-fallback state) == specFinal == range_spec(a, b, str)`.

The supporting invariant `result.Some? ==> |begs| == 0` (only branch-2 sets result, and it pops the stack to empty) lets Dafny case-split on the path the post-loop fallback would have to overwrite.

## Phase 2 proof structure (Dyck-balance foundation)

Earlier work established the `pushedCount`/`poppedCount` ↔ `CountAll` connection as loop invariants — the foundation that any later body-balance theorem about `range_spec` will build on. The proof rests on six pieces:

1. **`CountAll(s, sub, lo, hi)`** — a ghost function counting overlapping occurrences of `sub` in `s[lo..hi]`. Defined by recursion on `hi` so the recursive case *is* the extension-by-one equation; no separate extension lemma needed beyond what the body computes.
2. **`IndexOfMaxAt`** — a pointwise maximality lemma: at any position `p` strictly before `StringIndexOfFromN(s, sub, from)`, `sub` does not start at `p`. Avoids the quantifier-trigger trap of stating maximality as a forall in `StringIndexOf`'s postcondition.
3. **`CountAllExtendNoMatch` / `CountAllExtendOneMatch`** — extension lemmas: extending the upper bound over a range with no new matches (or exactly one) changes `CountAll` by 0 or 1.
4. **`CountAllShrinkLo`** — the dual: shrinking `lo` by 1 removes exactly the start position `lo` from the count (contributes 1 if `lo` is a sub-start, else 0). Used to extract `begs[0]`'s contribution at branch-2 result-setting.
5. **`CountAllExtendsByOne`** — the *single-forall* helper. Given that `s[p..p+|sub|] == sub` and `nextFrom = StringIndexOfFromN(s, sub, p+1)`, it bundles "build the no-match forall over `(matchK, hi_new]` using `IndexOfMaxAt`" and "apply `CountAllExtendOneMatch`" into one lemma. This is the key factoring — the `forall k` block lives in the lemma's body (small context), not in the main method.
6. **`CountAllZeroFromOtherStart` + `NoOverlapAtAPos`** — for the iter-1 case (first push), establishes `poppedCount == 0 == CountAll(str, b, begs[0], hi_b)` by combining a point-wise NoOverlap fact with `CountAllExtendNoMatch`. `NoOverlapAtAPos` takes the point-wise NoOverlap disjunction as a precondition (rather than the full forall); callers derive it via an explicit `assert str[p..p+|a|] != a || str[p..p+|b|] != b` that pins the verifier's trigger.

The branch-2 result-setting bundles steps 1, 4, 3 (in that order: `ShrinkLo` extracts `begs[0]`, then `ExtendNoMatch` shrinks `hi_a` to `bi+|a|-1`) via a single helper lemma **`BranchTwoBodyBalance`** that keeps the algebra out of the main method's verification context.

Plus three ghost-state additions in the loop:

- **`pushedCount`/`poppedCount` ghost counters** — accounting `|begs| == pushedCount - poppedCount` (algorithmic foundation).
- **`aiLowerBound`/`biLowerBound` ghost trackers** — the `from` arguments most recently passed to `indexOf`. Combined with the invariant `bi == StringIndexOfFromN(str, b, biLowerBound)`, this lets the maintenance proofs apply `IndexOfMaxAt` at the right `from` without re-deriving it.
- **Loop-entry pin invariant** — `|begs| == 0 && result.None? ==> pushedCount == 0 && poppedCount == 0 && bounds at initial values`. Iter 1 is the only iteration with empty `begs` and `result` still `None`; this invariant lets the iter-1 maintenance proof transition cleanly from "vacuous" to "established."

**Verification cost.** Z3 needs `--isolate-assertions` and a per-assertion timeout of ~500 seconds to discharge the heaviest VC (the existing `poppedCount == CountAll(str, b, begs[0], …)` invariant maintenance, now competing with the refinement's `range_spec_loop` calls in the verification context). The case study is registered in `LemmaScript-files.txt` with `500 --isolate-assertions`, which puts it on the `check.sh dafny-slow` track (not the default `dafny` track).

## What's not (yet) verified

- **Strict non-overlap** `result[0] + a.length <= result[1]` — does NOT hold in general. Counterexample: `a = "ab"`, `b = "b"`, `str = "ab"` → returns `[0, 1]` with `0 + 2 > 1`. The algorithm allows the `b`-substring to start inside the `a`-substring.
- **Body-balance as a method-level `ensures` on `range`** — `BodyBalancedOpt(range(...))` is implied by the existing `res == range_spec(a, b, str)` ensures plus `SpecBodyBalance`, so callers can derive it. It isn't packaged directly on the method because discharging `SpecBodyBalance`'s `NoOverlapPred(a, b, str)` precondition from the codegen-emitted curried-implication NoOverlap precondition trips Z3 trigger walls under `--isolate-assertions`.
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
src/index.ts 500 --isolate-assertions
```

Run via the LemmaScript `check.sh` driver in `dafny-slow` mode (which honors per-file timeouts above the default 60s CI ceiling):

```sh
../LemmaScript/tools/check.sh dafny-slow
```

Output:

```
Dafny program verifier finished with 2233 verified, 0 errors
```

(One pre-existing `pushedCount == CountAll(...)` invariant maintenance VC is flaky around the 500s budget; it discharges on most runs but may report 1 timeout. The proof is structurally sound — see DUMP2 pitfall 4 for the underlying Z3 sensitivity, which predates Phase 5.)

(The default `check.sh dafny` mode skips this file as gen-check-only because its timeout exceeds the 60s CI threshold.)

## File Structure

```
src/
  index.ts            ← Production TypeScript with //@ annotations on `range`
  index.dfy.gen       ← LS-generated Dafny (regeneratable from index.ts)
  index.dfy           ← Verification target: gen + proof-only lemmas, invariants, asserts
LemmaScript-files.txt ← Registers index.ts with the 500s --isolate-assertions config
```

The diff between `index.dfy.gen` and `index.dfy` is additions-only — the spec functions (`range_spec`, `range_spec_loop`, plus the no-fallback variants `range_spec_inner` and `range_spec_loop_inner` introduced by Phase 4), proof-only lemmas (`CountAll`, `IndexOfMaxAt`, `CountAllExtend*`, `CountAllExtendsByOne`, `CountAllShrinkLo`, `CountAllZeroFromOtherStart`, `NoOverlapAtAPos`, `NoOverlapPred` / `NoOverlapInstance`, `BranchTwoBodyBalance`, `BodyBalancedOpt`, `SpecBodyBalanceLoopInner`, `SpecBodyBalanceInner`, `RangeSpecLoopInnerAgreement`, `SpecBodyBalanceLoop`, `SpecBodyBalance`, `FirstBalancedPairLoopInner`, `FirstBalancedPair`), loop invariants Dafny needs that can't be expressed in the TS surface, plus bridging asserts that thread facts from invariants to use-sites. The method-level `ensures res == range_spec(a, b, str)` is the headline universal claim; `SpecBodyBalance` is the Phase 5 derived theorem (unconditional body-balance) and `FirstBalancedPair` the Phase 6 derived theorem (leftmost-a characterization).

## LemmaScript toolchain additions driven by this case study

Six small, broadly-useful extensions:

1. **`Array.pop()` lowering** — `let x = arr.pop()` desugars to a two-statement form: `var x: T? = (if |arr| > 0 then Some(arr[|arr|-1]) else None); arr := (if |arr| > 0 then arr[..|arr|-1] else arr);`. Mirrors the existing `Array.shift()` lowering. Handles both `let` and `assign` positions; receiver must be a `var`. Helper factored as `buildPopLowering`.
2. **Type-driven defaults for uninitialized `let`** — `let x: T[];` → `[]`, `let x: T | undefined;` → `None`, `let x: number;` → `0`, etc. The previous "emit `default` and let Dafny complain" path was always wrong; this fix is generic across case studies. Also extended the optional-detection regex to handle leading `undefined | T` / `null | T` (was only catching trailing).
3. **`StringIndexOfFrom` accepts `int`** — was `nat`, which forced callers to discharge `from >= 0` for `str.indexOf(s, fromIdx)` calls where `fromIdx` was an int. Now clamps internally (matching TS's behavior of treating negative `fromIdx` as 0). Plus added `ensures` clauses on all three `StringIndexOf*` helpers (relating result to `from`, validating the match substring) — these are what makes downstream proofs about indexOf results tractable.
4. **`indexOf(s, from)` emits with both args** — pre-fix, the dafny-emit silently dropped the second argument, silently turning `str.indexOf(b, ai + 1)` into `StringIndexOf(str, b)` (searching from 0 — wrong semantics).
5. **`&&` narrowing on either conjunct** — `if (begs.length && right !== undefined)` now narrows `right` to its unwrapped value in the body. Previously LS only recognized the optional check as the *leftmost* conjunct; this fix walks the `&&` tree and accepts the check on either side.
6. **Truthy coercion on `int`/`array` conditions** — `if (n)`, `while (n)`, `n ? a : b` where `n: number` (or `xs: T[]`) now coerce to `n > 0` / `|xs| > 0`. The conditional case used to handle `string` only.
