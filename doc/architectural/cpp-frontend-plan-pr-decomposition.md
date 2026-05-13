\file

Detailed plan: PR decomposition strategy for cpp11-parser-rework-squashed

# Detailed plan: PR decomposition strategy

**Owner:** — (to be assigned, typically repository maintainer)
**Status:** Proposed
**Parent documents:**
- `doc/architectural/cpp-frontend-review.md` (the review)
- `doc/architectural/cpp-frontend-plan-lazy-elaboration.md` (future work)
- `doc/architectural/cpp-frontend-plan-target-type-threading.md` (future work)

## 1. Problem statement

`cpp11-parser-rework-squashed` carries **465+ commits** ahead of
`origin/develop`.  PR #8878 against `diffblue/cbmc` is a DRAFT marker
("[Individual PRs to follow]" in the title) precisely because landing
it as a single PR is impractical:

- Review bandwidth: 465 commits × average 3 files × average 30 lines
  is ~40k+ lines of net change.
- CI blast radius: a single revert on develop is all-or-nothing for
  the entire branch.
- Bisection: if a regression surfaces after merge, narrowing it
  across 465 commits is painful.
- Standard conformance rationale: each fix has a standard-clause
  anchor that a reviewer wants to verify; 465 such verifications in
  a single PR is infeasible.

This plan describes how the branch gets split into logically coherent
PRs that each land on `develop` independently.

## 2. Guiding principles

1. **Each PR should be reviewable end-to-end by one reviewer in one
   sitting** (rough target: ≤ 1000 LoC net change, fewer if the
   domain is subtle).
2. **Each PR should pass CI independently.**  No "this PR depends on
   another unmerged PR" unless the dependency is explicit and in
   flight.
3. **Each PR should have a standard-clause-anchored story.**  The
   reviewer should be able to read the PR description and see which
   N5008 clause motivates the change.
4. **Each PR should have a regression test** or an explicit "no test
   possible at this layer" justification.
5. **Revert units:** PRs should be sized so that reverting one
   doesn't cascade to dependent work.

## 3. Decomposition — stacking order

PRs roughly in the order they should land, with rough sizing.  Each
entry lists the commits on the branch that it consists of (using the
`ac830e7ef6..bf79ab84e3` range).

### Tier A — infrastructure and primitives (small, foundational)

**PR A1 — `sfinae_contextt` primitive + consolidation**
- Commits: `7160102bc3`, `2d0e466bd7`, `f38f2b67bc`, `a437aacd7d`
  (5 commits, ~400 LoC net).
- Story: introduce an RAII guard for [temp.deduct]/8 immediate
  contexts, consolidate 12 hand-rolled `null_message_handlert` +
  error-count save/restore patterns, and generalise the P3a
  duration-specific guard.
- Tests: existing CORE + KNOWNBUG (regression: no new behaviour).
- Review surface: one new primitive + mechanical call-site
  conversions.
- Risk: low.

**PR A2 — architectural review document**
- Commits: `18e1334e59`, `9202e11a67`, `355de51611`, the three plans
  documents (lazy-elaboration, target-type-threading, this PR-
  decomposition plan).
- Story: capture the as-is architecture, its weaknesses, and the
  medium/long-term plans.  No code change.
- Review surface: docs only.
- Risk: none.

### Tier B — focused bug fixes anchored on specific standard clauses

Each of these is a single-commit or small-cluster PR where the fix
is self-contained and the story is specific.

**PR B1 — `cpp11_deduct_funcaddr` via probe-retry helper**
- Commits: `d612fe6dac`, `cf8be98c37`, `a5a4b9f156`, `bf79ab84e3`
  (4 commits, ~200 LoC).
- Story: implement [temp.deduct.funcaddr]/1 for plain function-
  pointer target types, promote `cpp11_deduct_funcaddr` from
  KNOWNBUG to CORE.
- Tests: `regression/cbmc-cpp/cpp11_deduct_funcaddr/` already
  updated in the branch.
- Risk: low.

**PR B2 — `cpp11_future_header` SIGSEGV guard**
- Commit: `df5f5d955e`.
- Story: null-guard for empty declarator-name sub in
  `convert_non_template_declaration`'s trailing-return-decltype
  path.
- Tests: MSVC preprocessed-header run of `cpp11_future_header`.
- Risk: low.

**PR B3 — `cpp14_chrono_basic` + `<filesystem>` via common_type
tolerance + alias cycle-break**
- Commits: `2e8e74f8ed`, `702df7c722`, `09e5625681`.
- Story: tolerate self-referential `common_type_t<SelfClass>`
  member types during class-template instantiation per
  [temp.inst]/3; break mutual-recursion cycles in
  `resolve_template_alias` for SFINAE-guarded aliases per
  [temp.alias].
- Tests: MSVC preprocessed headers.
- Risk: low.

**PR B4 — destructor + enum + SFINAE absorption fixes**
- Commits: `5e7efee580`, `7a9154a46e`, `56c27ea9d3`, `c8f322f213`,
  `01507a3e6d`, the KNOWNBUG test.desc updates (`cf8be98c37`,
  `b37b68b273`).
- Story: three related front-end fixes: destructor-synthesis
  fall-back to components list, bare `enum class X;` forward
  declarations per [dcl.enum]/5, silent-throw of template-only
  no-match per [temp.deduct]/8.
- Tests: existing regressions + the updated KNOWNBUG test.desc
  patterns.
- Risk: low–medium (touches the resolver's emission path).

### Tier C — dog-food / tooling infrastructure

**PR C1 — dog-food harness + CI job**
- Commits: `4648a540b8` + dependent ancestors (6b09016f4a, ancestors
  adding scripts/dogfood_goto_cc.sh).
- Story: add the dog-food harness as a report-only CI signal.
- Tests: the CI job itself validates.
- Risk: low (report-only).

**PR C2 — documentation updates**
- Commits: `fd309f51cd`, `102d67b323`, `16218c0909`, `fc2a2c656d`,
  dogfood and CI_KNOWN_FAILURES updates.
- Story: document the known failures and fix progress.
- Risk: none.

### Tier D — the older branch history

The earlier ~400 commits on the branch (from `ac830e7ef6` up to
roughly `e7080a017e`) cover the bulk of the C++11–C++17 parser
rework.  Tier D is where the real PR-decomposition investment is,
and it happens *after* Tiers A–C land because those are easier to
agree on and establish the review pattern.

Breaking Tier D into PRs is a sub-project; a useful first cut:

- **D1** — C++11 core language: `auto`, `decltype`, rvalue references,
  variadic templates (~70 commits).
- **D2** — C++14/17 additions: generic lambdas, `if constexpr`,
  structured bindings (~50 commits).
- **D3** — Template-argument deduction refactor: [temp.deduct.call],
  [temp.deduct.type] (~40 commits).
- **D4** — Partial specialisation + concepts machinery (~30 commits).
- **D5** — SFINAE + substitution (~30 commits; subsumed by Tier A in
  part).
- **D6** — STL instance handling (unordered_map rebind, basic_string
  ctors, etc.) (~80 commits).
- **D7** — Concrete test additions + KNOWNBUG list + CI workflow
  changes (~50 commits).
- **D8** — Fixes motivated by MSVC preprocessed headers (~40 commits).

Each of D1–D8 is a dedicated PR stream of 3–10 sub-PRs.

### Tier E — future work from the plans

Once Tier D is landing, the medium-term plans become concrete PR
streams:

- **E1** — lazy class-body elaboration (per
  `cpp-frontend-plan-lazy-elaboration.md`, 5 phases, ~30 commits
  across 3–4 weeks of work).
- **E2** — target-type threading (per
  `cpp-frontend-plan-target-type-threading.md`, 6 phases, ~20
  commits across ~2 weeks).
- **E3** — SFINAE outcome type reshape (deferred until E1 completes).
- **E4** — Two-phase name lookup + POI tracking (long-term).

## 4. Sequencing

```
Tier A (infra/docs)        ─── no deps, land first
   │
Tier B (focused bugfixes)  ─── depends on A1 (sfinae_contextt)
   │
Tier C (dog-food harness)  ─── indep of B; after A2 (review doc) for context
   │
Tier D (older history)     ─── the bulk; 6–10 weeks of review cycles
   │                           sub-PRs can land in parallel streams
Tier E (future work)       ─── E2 can start after A1; E1 after E2 or in
                                parallel with a different owner;
                                E3/E4 after E1
```

## 5. Per-PR checklist (to apply to every sub-PR)

1. PR description cites the specific N5008 clauses the change
   implements.
2. PR description includes the "before" and "after" behaviour as a
   small reproducer or test diff.
3. PR has a new regression test or an explicit justification for
   why none is needed at this layer.
4. cpplint + clang-format-15 clean.
5. `ctest -L CORE` clean on all CI platforms.
6. Dog-food `--expand` delta reported in the PR description (even
   if the delta is zero).
7. If retiring a workaround from the branch: the workaround removal
   is in the *same* PR as the principled fix.

## 6. Migration logistics

### Branch layout

- Keep `cpp11-parser-rework-squashed` as the **integration branch**.
  It tracks the full state that has passed CI.
- For each planned PR (Ax, Bx, Cx, Dx.y), create a topic branch
  `cherrypick/<pr-name>` rebased onto current `origin/develop`.
  Cherry-pick the relevant commits (or squash them if they are
  intermediate states).
- Open the PR from the topic branch.  Iterate with reviewers.
- When it lands on `develop`, drop the corresponding commits from
  the integration branch via `git rebase --interactive --onto` or
  a merge of `origin/develop` back in.

### Conflict handling

As PRs land, the integration branch needs rebasing.  Expected
conflicts:
- Minor: files touched by both a landing PR and a later-tier PR
  that still sits on the branch.  Resolve on each rebase.
- Major: if a reviewer asks for a design change that reshapes the
  primitive (e.g. `sfinae_contextt` signature change).  Rare if
  Tier A is reviewed carefully.

### Test preservation

Every PR must ship with the regression tests that exercise its fix.
Tests that already exist on the branch but weren't written by the
PR's commits: cherry-pick into the topic branch alongside the fix
commits.  A fix without a test gets pushback in review and slows
the landing cadence.

## 7. Metrics and gates

**Target cadence:** 2–4 PRs merged per week once the pipeline is
stable.  At 80 total PRs estimated, that is a 6-month landing
window.

**Gates that the integration branch must keep meeting:**

- CORE + KNOWNBUG regressions: 100% green.
- MSVC preprocessed headers: 26/26.
- Dog-food `--expand`: no regression (neither on individual files
  that went OK → FAIL nor on the aggregate pass count).
- cpplint + clang-format-15: clean on every diff.

**Individual PR acceptance criteria:**

- Reviewed by at least one maintainer who is not the author.
- All CI checks green.
- If a PR changes the pass-rate metric, the change is reported in
  the PR description.

## 8. Risks

| risk | probability | severity | mitigation |
|------|-------------|----------|------------|
| Reviewer capacity can't keep up with proposed cadence | medium | high | Tier A (small, mechanical) is the first filter; if even Tier A is slow, the cadence target is adjusted downward. |
| A landed PR regresses later on `develop` due to a change outside our branch | medium | medium | Each topic branch is rebased on a fresh `develop` before the PR opens; CI verifies at rebase time. |
| Tier D PRs turn out to need different decomposition than the initial sketch | high | low | The sketch is a first cut; refine as Tier A–C land and reviewers provide feedback on what logical boundaries they find easiest to review. |
| Integration branch CI drifts (new failures appear on the branch that weren't there at push time) | medium | medium | Poll CI daily; at least one maintainer monitors the integration branch status. |

## 9. What this document is not

- **Not** a commitment to the exact 80-PR breakdown.  The Tier D
  cut, especially, is a first sketch.  Reviewer feedback will
  reshape it.
- **Not** a timeline commitment.  The 6-month window is a rough
  capacity estimate; actual landing depends on reviewer bandwidth
  and the quality of each PR.
- **Not** a replacement for individual PR design discussions.
  Each PR still needs its own description, tests, and review.

## 10. Deliverables from this plan

Once the Tier A and B PRs have landed:
1. `sfinae_contextt` is part of `develop`, retiring ~20 hand-rolled
   guards.
2. The architectural review document is part of `develop` for all
   contributors to reference.
3. `cpp11_deduct_funcaddr` is CORE, not KNOWNBUG.
4. MSVC preprocessed headers at 26/26 on `develop`'s CI.
5. The dog-food harness is a CI signal on `develop`.

Those five deliverables alone represent a material improvement to
the front end and a visible demonstration that the integration
branch can be landed incrementally.
