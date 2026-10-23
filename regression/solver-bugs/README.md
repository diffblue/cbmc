# Solver-bug regression tests

Programs on which cvc5 gives CBMC a wrong answer. Each directory holds
`main.c` and CORE descriptors without options:

| Descriptor | First line | Expected output |
|---|---|---|
| `sat.desc` | `CORE witness` | the correct verdict from CBMC's SAT back end |
| `cvc5-<version>.desc` | `CORE cvc5-<version>` | that cvc5 version's verdict |

CI runs `sat.desc` with `cbmc` and each version descriptor once with
`cbmc --cvc5`. The cvc5 version CI uses is always included; if it has no
version descriptor for a test, CI runs that test's `sat.desc` with cvc5.
Each recorded version needs its SHA-256 in `.github/actions/install-cvc5`.
After every test job passes, CI adds one Markdown report to the run summary.

## Running

```
python3 ../../scripts/solver_bugs.py matrix --ci-cvc5 1.3.4
python3 ../../scripts/solver_bugs.py run
python3 ../../scripts/solver_bugs.py run --cvc5 1.4.1 --ci-cvc5 1.3.4
python3 ../../scripts/solver_bugs.py report --ci-cvc5 1.3.4
```
