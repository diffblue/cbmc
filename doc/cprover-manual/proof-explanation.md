[CPROVER Manual TOC](../)

# Proof Explanations

When CBMC proves that all properties hold, it normally just reports
`VERIFICATION SUCCESSFUL`. The `--proof-explanation` option makes CBMC
additionally show *why* the properties hold — which assignments and
assumptions in your code are responsible for the proof.

## Usage

```sh
cbmc program.c --proof-explanation
```

The option works with all verification modes (bounded model checking,
coverage analysis) and all solver backends (SAT, SMT).

## Reading the Output

The proof explanation has two sections:

### Proof Explanation

Lists the program steps that contribute to the proof. Each line shows:
- `[core]` — this step is in the solver's unsat core (essential to the proof)
- The step type: `[assignment]`, `[assumption]`, or `[constraint]`
- The source file and line number
- The SSA expression (the symbolic value)

Example:
```
Proof explanation:
  [core] [assumption] example.c:5 ¬(x ≥ 10)
  [core] [assignment] example.c:6 y = x + 1
```

This means: the proof relies on the assumption `x < 10` (line 5) and
the assignment `y = x + 1` (line 6).

### Proof Invariants

Groups the proof explanation by variable, showing what constraints each
variable satisfies:

```
Proof invariants:
  x: ¬(x ≥ 10)
  y: y = x + 1
```

## Examples

### Simple constant proof

```c
int main() {
  int x = 5;
  assert(x > 0);
}
```

Output:
```
Proof explanation:
  [core] [assignment] example.c:2 x = 5

Proof invariants:
  x: x = 5
```

The proof relies solely on `x = 5`, which makes `x > 0` trivially true.

### Assumption-based proof

```c
int main() {
  unsigned x;
  __CPROVER_assume(x < 10);
  unsigned y = x + 1;
  assert(y > 0);
  assert(y <= 10);
}
```

Output:
```
Proof explanation:
  [core] [assumption] example.c:3 ¬(x ≥ 10)
  [core] [assignment] example.c:4 y = x + 1

Proof invariants:
  x: ¬(x ≥ 10)
  y: y = x + 1
```

The proof uses the assumption `x < 10` and the computation `y = x + 1`.
Together these imply `y` is between 1 and 10, satisfying both assertions.

### Explaining unreachable code (with --cover)

```sh
cbmc program.c --cover location --proof-explanation
```

When a coverage goal is FAILED (unreachable), the proof explanation shows
why that code location cannot be reached. For example, if `x` is
constrained to `[0, 50]`, the branch `if(x > 100)` is unreachable, and
the explanation will show the constraint on `x`.

## Limitations

- **SSA names**: The output uses CBMC's internal SSA variable names
  (e.g., `main::1::x!0@1#2`). The variable name before `::` is the
  function, and the name after the last `::` is the local variable.
  The `#N` suffix is the SSA version number.

- **Loop invariants**: For programs with loops, the explanation shows
  the concrete unrolled assignments rather than synthesized loop
  invariants. This can be verbose for deeply unrolled loops.

- **Per-property granularity**: The explanation covers all proved
  properties together, not each property individually. When multiple
  properties hold, the explanation shows the union of all contributing
  steps.

- **Solver dependence**: The quality of the explanation depends on the
  SAT/SMT solver's unsat core. Different solvers may produce different
  (but equally valid) explanations.
