# External benchmark sources for corpus widening

This document inventories external benchmark sources identified
from the Konrad/Scholl/Onderka literature thread (Armin's June
2026 review). It gives concrete download URLs, sizes, content
descriptions, and a tiered acquisition plan.

Current state: our SMT-LIB sample is **66 benchmarks** in
`bench-multiplication/smt-comp-sample/` (drawn from older
SMT-LIB releases) plus a 102-benchmark synthetic
`bench-multiplication/smt-comp/` set crafted for the paper.

## STATUS UPDATE (2026-06-01): acquisition done

The file system was extended to 122 GB free, removing the disk
constraint. We acquired:

- **Tier A done**: full SMT-LIB 2024 QF\_BV extracted (35 GB,
  46,191 benchmarks; 15,435 contain `bvmul` and are `unsat`).
  Staged at `/home/ubuntu/bench-staging/non-incremental/QF_BV/`.
- **Tier B downloaded but blocked**: all three Konrad archives
  pulled and verified, but no AIG→SMT-LIB converter is present
  (`abc`/`aigtoaig`/`yosys` absent). These are gate-level
  (Item 7) material; deferred until a converter is installed.

**Headline outcome**: triaging the full QF\_BV corpus revealed
the **`float` family** (FP-as-BV, Haller-Griggio-Brain-Kroening
FMCAD 2012) where our solver **dominates**: 68/75 solved vs
Bitwuzla 51, cvc5 6, with **18 confirmed unique
wins-beyond-all-solvers**. See
`bench-multiplication/float-fp2bv/RESULTS.md`. This adds 18 to
the paper's previous count of 4 wins-beyond-all-solvers.

## Tier A — SMT-LIB 2024 QF\_BV (highest priority)

**Source**: SMT-LIB release 2024 non-incremental benchmarks,
Zenodo `10.5281/zenodo.11061097`, curated by Preiner, Schurr,
Barrett, Fontaine, Niemetz, Tinelli.

- Direct URL:
  `https://zenodo.org/records/11061097/files/QF_BV.tar.zst?download=1`
- Compressed: 1.7 GB
- Estimated uncompressed: 10–30 GB (zstd typically 10–20× on
  SMT-LIB)
- Total claimed unsat in 2024 release (from Roole/Roolean
  paper): 27 758 benchmarks claimed unsatisfiable. Roole
  produces certificates for 17 433 (62.8%) within 1200 s + 8 GB.

**Why this matters for us**: this is the canonical QF\_BV
benchmark suite that bv\_decide, Bitwuzla, and Roole all run
against. Our paper currently positions itself against bv\_decide
on a 66-benchmark sample; expanding to (a strategic sample of)
the full 27 758 set would provide much stronger statistical
backing.

**Acquisition plan**:

1. Download `QF_BV.tar.zst` (1.7 GB).
2. Stream-decompress + list the archive without full extraction
   to understand directory structure.
3. Extract the multiplication-heavy subdirectories first
   (typically those under `2017-BuchwaldFried/`,
   `wienand-cav2008/`, `2018-Goel-hwbench/`, and similar
   contributor-named directories that already appear in our
   66-sample). Compare size; widen incrementally.
4. Run our solver on the wider sample to identify failure
   patterns; classify against Item 10's four gates.

**Acquisition cost**: 1–2 hours of download + processing on
this machine. Storage: ~5 GB selective extraction.

## Tier B — Konrad/Scholl gate-level benchmark archives

**Source**: `https://abs.informatik.uni-freiburg.de/src/projects_view.php?projectID=24`
(VerA project page).

Three downloadable archives:

- `FMCAD22_tools_and_benchmarks.zip` (378 MB) — divider
  benchmarks accompanying the FMCAD 2022 Konrad-Scholl-Mahzoon
  et al. paper (which is the conference version of `KSM_2024`
  we already have). Contains:
  - non-restoring divider benchmarks at bit widths up to 512
    (clean and `non-res2` optimised variants)
  - restoring divider benchmarks
  - Their `DDCO` tool binary (Linux Ubuntu 20.04)
- `FMCAD24_tool_benchmarks_experimental_data.zip` (154 MB) —
  multiplier benchmarks accompanying the Konrad-Scholl FMCAD
  2024 paper (conference version of `alexander_konrad_fmsd`).
  Contains:
  - 192 64-bit multipliers from the aoki-benchmark set
    (no longer available online elsewhere)
  - 28 multipliers from GenMul
  - 90 multipliers from multgen (truncated and full)
  - `DynPhaseOrderOpt` tool binary
- `FMSD25_tool_and_data.zip` (951 MB) — extended journal
  version of the FMCAD 2024 work. Contains the FMCAD 2024
  benchmark set plus additional bit widths (16 → 256) and
  industrial Synopsys-generated multipliers (4 → 256-bit).

**Why this matters for us**: All three archives contain
**gate-level AIG/Verilog** benchmarks, not SMT-LIB QF\_BV. To
use them in our framework we would need an AIG → QF\_BV
translation step. Bitwuzla, Boolector, and `aigtoaig` all
provide this. The translation produces SMT formulas of the form
"miter circuit equivalent to specification polynomial" which
exercises a different fragment than our usual workload.

**Acquisition plan** (deferred until Tier A is processed):

1. Download `FMCAD24_tool_benchmarks_experimental_data.zip`
   first (smallest, most directly relevant).
2. Inventory the AIG file list.
3. Convert a small sample (e.g.\ four 16-bit multipliers, one
   from each architecture family) to QF\_BV via
   `bitwuzla --print-formula <aig>` or equivalent.
4. Run our solver, classify failures.
5. Decide whether to pursue larger samples or the FMSD25
   extended set.

**Acquisition cost**: 1 day if scope is bounded to a 16- and
32-bit multiplier sample; 3–5 days if scope expands to include
the 64-bit set or the divider benchmarks.

## Tier C — Multiplier and divider generators

These are reproducible generators rather than fixed corpora:

- **GenMul** — `http://sca-verification.org/genmul`. 28
  architectural variants × any bit-width. Generates AIG.
  Currently returns `403 Forbidden` from this server; need to
  check the JKU mirror at `https://ics.jku.at/research/sca-verification/genmul/`.
- **multgen** — `https://github.com/temelmertcan/multgen`.
  Generates 90 different 64-bit multipliers. Includes truncated
  multipliers (modular by $2^n$).
- **Mertcan Temel's verilog generators** — referenced in the
  Konrad-Scholl FMSD 2026 paper §5.4 industrial section. Used
  Synopsys Design Compiler to generate multipliers at bit
  widths 4 → 256.

**Why this matters for us**: Generators are useful to construct
**parameterised** benchmark families to exercise specific
patterns we want to test (e.g.\ "what happens at bit-widths
beyond what aoki/GenMul publish"). They also let us measure
scaling rather than rely on fixed-bit-width snapshots.

**Acquisition plan** (deferred until Tier A and Tier B are
processed):

1. Pull each generator's source.
2. Generate small sweeps (8/16/32/64 bits) per architecture.
3. Convert AIG → QF\_BV.
4. Add as a `bench-multiplication/genmul-sweep/`
   sub-directory.

## Tier D — Roole/Roolean artefact

**Source**: Zenodo `10.5281/zenodo.20120023`.

Contains scripts for partial local evaluation and visualisation
of Roole+Roolean. Useful primarily for *reproducing* Roole's
SMT-LIB 2024 evaluation (which is Tier A above), not as a new
benchmark source.

## Tier E — Fuzzer-generated buggy circuits

Konrad-Scholl FMSD 2026 §5.6 uses MultAIGenFuzzer +
AIGoFuzzing to construct buggy multipliers. These are SAT
counterexample-detection benchmarks (the fuzzer mutates a
correct circuit; the verifier should report SAT with a
counterexample). They are *out of scope* for our current paper,
which is only about UNSAT verdicts.

## Recommended acquisition order

1. **Tier A** (SMT-LIB QF\_BV) — pull, inventory, classify the
   multiplication-heavy subset.
2. **Tier B partial** (FMCAD24 multipliers) — pull, convert a
   16- and 32-bit sample, run.
3. After running both: *re-prioritise Item 10*. The new failure
   patterns from a 100×-larger corpus may expose gates we
   haven't yet considered.
4. **Tier B full / Tier C** — only if the above leaves
   open questions that a larger corpus would answer.

## Decision points

- **Disk budget**: 26 GB free on this machine. Tier A
  selective extraction fits; Tier B requires another ~2 GB.
  Tier C is open-ended.
- **AIG → SMT-LIB conversion**: Bitwuzla is already on this
  machine; should be a one-liner per AIG. Worth scripting up
  before Tier B.
- **Run-time budget for evaluation**: 60 s per benchmark × 1000
  benchmarks ≈ 17 hours wall-time. We'd need to either
  parallelise (cluster?), shorten the timeout, or sub-sample.
