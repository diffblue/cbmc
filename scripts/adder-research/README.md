# Per-Addition Encoding Research Setup

This directory contains tools for focused research on adder encodings
at the single-addition level, isolating the encoding from problem-level
effects (loop unrolling, assertion framework, etc.).

## Approach

Instead of benchmarking full CBMC runs (which mix encoding time, SSA
conversion, and solver time), we work directly with DIMACS CNF files
representing a single 32-bit addition with various constraints.

## Files

- `gen_single_add.sh` — Generate DIMACS for one addition with a given encoding
- `compare_encodings.sh` — Run all encodings on all micro-benchmarks
- `analyze_proof.sh` — Extract proof statistics from CaDiCaL traces
- `micro_benchmarks/` — Focused single-addition test cases
