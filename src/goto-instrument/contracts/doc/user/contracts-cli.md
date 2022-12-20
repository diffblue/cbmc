# Command Line Interface for Code Contracts {#contracts-user-cli}

## Applying loop and/or function contracts transformations (without the dynamic frames method)

The program transformation takes the following parameters:

```
goto-instrument [--apply-loop-contracts] [--enforce-contract <function>] (--replace-call-with-contract <function>)* in.gb out.gb
```

Where:
- `--apply-loop-contracts` is optional and specifies to apply loop contracts globally;
- `--enforce-contract <function>` is optional and specifies that `function` must be checked against its contract.
- `--replace-call-with-contract <function>` is optional and specifies that all calls to `function` must be replaced with its contract;

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


