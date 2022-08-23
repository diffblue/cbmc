# Command Line Interface for Code Contracts {#contracts-user-cli}

## Applying loop and/or function contracts transformations (without the dynamic frames method)

The program transformation takes the following parameters:

```
goto-instrument [--apply-loop-contracts] [--enforce-contract f] (--replace-call-with-contract g)* in.gb out.gb
```

Where:
- `--apply-loop-contracts` is optional and specifies to apply loop contracts globally;
- `--enforce-contract f` is optional and specifies that `f` must be checked against its contract.
- `--replace-call-with-contract g` is optional and specifies that all calls to `g` must be replaced with its contract;

## Applying the function contracts transformation (with the dynamic frames method)

The program transformation takes the following parameters:

```
goto-instrument --dfcc harness [--enforce-contract f] (--replace-call-with-contract g)* [--apply-loop-contracts] in.gb out.gb
```

Where:
- `--dfcc harness` specifies the proof harness (i.e. the entry point of the analysis);
- `--enforce-contract f` is optional and specifies that `f` must be checked against its contract.
- `--replace-call-with-contract g` is optional and specifies that all calls to `g` must be replaced with its contract;

