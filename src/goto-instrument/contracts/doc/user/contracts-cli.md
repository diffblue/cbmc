# Command Line Interface for Code Contracts {#contracts-user-cli}

## Applying loop and/or function contracts transformations (without the dynamic frames method)

The program transformation takes the following parameters:

```
goto-instrument [--apply-loop-contracts] [--enforce-contract <function>] (--replace-call-with-contract <function>)* in.gb out.gb
```

Where:
- `--apply-loop-contracts` is optional and specifies to apply loop contracts globally;
- `--enforce-contract <function>` is optional and specifies that `function` must be checked against its contract.
- `--replace-call-with-contract <function>` is optional and specifies that all calls to `function` must be replaced with its contract.
  It is an error if no applicable contract can be found.

## Applying the function contracts transformation (with the dynamic frames method)

The program transformation takes the following parameters:

```
goto-instrument --dfcc harness [--enforce-contract <function>[/<contract>]] (--replace-call-with-contract <function>[/<contract>])* in.gb out.gb
```

Where:
- `--dfcc harness` specifies the proof harness (i.e. the entry point of the analysis);
- `--enforce-contract <function>[/<contract>]` is optional and specifies that `function` must be checked against `contract`.
  When `contract` is not specfied, the contract is assumed to be carried by the `function` itself.
- `--replace-call-with-contract <function>[/<contract>]` is optional and specifies that all calls to `function` must be replaced with `contract`.
  When `contract` is not specfied, the contract is assumed to be carried by the `function` itself.
  It is an error if no applicable contract can be found (either because `contract` is specified but
  cannot be found, or because `contract` is not specified and `function` does not have an attached
  contract).

### Using function contracts by default

With dynamic frames, `--always-use-function-contracts` replaces each
reachable callee that has a contract with that contract:

```
goto-instrument --dfcc harness --enforce-contract function_under_test --always-use-function-contracts [--keep-function-body helper]* in.gb out.gb
```

The harness and the function selected by `--enforce-contract` or
`--enforce-contract-rec` retain their bodies. A callee that has a body but
no contract also retains it, and its own callees are selected in the same
way. `goto-instrument` lists every such callee with the message `Keeping
body of 'callee', which has no contract`. Contracts used for replacement
must still be verified separately.

`--always-require-function-contracts` implies
`--always-use-function-contracts` and makes a reachable callee that has a
body but no contract an error instead.

In both modes, the repeatable `--keep-function-body <function>` option
retains the body of the named function even if it has a contract. Names are
exact function identifiers in the GOTO model. An exception applies only to
the named function: its callees are still selected as described above.
Calls in replaced bodies are not followed.

Explicit `--replace-call-with-contract function/contract` mappings remain
supported and take precedence over automatic selection of `function`'s own
contract. Selecting the same function for replacement and for
`--keep-function-body` is an error, as is naming a nonexistent exception.

A function has a contract if its declaration has at least one
`__CPROVER_requires`, `__CPROVER_ensures`, `__CPROVER_assigns` or
`__CPROVER_frees` clause.

CBMC builtins, CPROVER C library models such as `malloc`, and other callees
without a body need no contract and retain their existing treatment: CBMC
uses the library model, or otherwise fails verification when the call is
reached.

Function pointers are removed before selecting replacements, so the policy
also applies to their possible target functions. Selection follows calls
conservatively and does not prove that a call site or target is executable.

These options require `--dfcc`, and `--keep-function-body` also requires
one of the other two. They are incompatible with `--inline` and
`--escape-analysis`, which can inline bodies before contract replacement, so
supply a GOTO binary with the original call boundaries.
