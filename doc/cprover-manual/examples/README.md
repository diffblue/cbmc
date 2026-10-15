# Java Modeling Constructs Examples

This directory contains example Java files demonstrating the use of fundamental
modeling constructs for JBMC verification.

## Files

- **`BankingExample.java`** - Complete example showing assertions, non-determinism, and assumptions
- **`AssertionExamples.java`** - Various assertion patterns and usage
- **`NondeterminismExamples.java`** - Examples of all non-deterministic value types
- **`AssumptionExamples.java`** - Comprehensive examples of using assumptions

## The CProver API

These examples use the `org.cprover.CProver` API. Its source of truth is the
[java-cprover-api](https://github.com/diffblue/java-cprover-api) project,
distributed as `cprover-api.jar`; do not copy the class into your project, just
put the jar on your classpath. In the CBMC tree the jar is built from the
`java-models-library` submodule:

```bash
git submodule update --init jbmc/lib/java-models-library
(cd jbmc/lib/java-models-library && mvn dependency:copy@copy-dependencies)
# -> jbmc/lib/java-models-library/target/cprover-api.jar
```

## Compiling the Examples

Compile against `cprover-api.jar` (the examples do not run on a regular JVM --
they throw `RuntimeException` -- they are meant to be analyzed with JBMC):

```bash
javac -cp /path/to/cprover-api.jar *.java
```

`test-compilation.sh` automates this; it accepts the jar path as an argument
(or via the `CPROVER_API_JAR` environment variable) and defaults to the in-tree
build location.

## Running JBMC on the Examples

To verify an example with JBMC, you need to specify the function to use as an
entry point:

```bash
# Example 1: Verify the banking example
jbmc BankingExample --function BankingExample.verifyTransfer

# Example 2: Verify mathematical properties
jbmc AssertionExamples --function AssertionExamples.mathematicalProperties

# Example 3: Verify the absolute value function
jbmc NondeterminismExamples --function NondeterminismExamples.verifyAbsolute

# Example 4: Test safe division
jbmc AssumptionExamples --function AssumptionExamples.testSafeDivide
```

> **Note:** Examples that exercise `java.lang.String` (such as
> `BankingExample.verifyWithObjects`, which calls `message.length()`) require
> the JBMC core models on the classpath. Add `--cp` pointing at
> `core-models.jar`, for example:
>
> ```bash
> jbmc BankingExample --function BankingExample.verifyWithObjects \
>   --cp <CBMC>/jbmc/src/java_bytecode/library/core-models.jar:.
> ```

## Common JBMC Options

When running JBMC, you may want to use these options:

- `--function <name>` - Specify the entry point function
- `--unwind <n>` - Set loop unwinding bound
- `--trace` - Show a counterexample trace if verification fails
- `--throw-runtime-exceptions` - Enable runtime exception checking

Example with options:

```bash
jbmc NondeterminismExamples \
  --function NondeterminismExamples.testPrimeCounter \
  --unwind 20 \
  --trace
```

## Understanding the Output

JBMC will report:

- **SUCCESS** - The property holds for all possible inputs
- **FAILURE** - Found a counterexample that violates the property
- With `--trace`, you'll see the specific input values that cause a failure

## Key Concepts

### Assertions
Use `assert` statements to specify properties you want to verify:
```java
assert x > 0 : "x must be positive";
```

### Non-determinism
Use `CProver.nondetXXX()` methods to model arbitrary inputs:
```java
int x = CProver.nondetInt();  // x can be any integer
```

### Assumptions
Use `CProver.assume()` to constrain the search space:
```java
CProver.assume(x >= 0 && x <= 100);  // only consider x in [0, 100]
```

## Tips for Writing Verification Harnesses

1. **Start with small ranges** - Constrain inputs to reasonable ranges to avoid
   state explosion:
   ```java
   int x = CProver.nondetInt();
   CProver.assume(x >= 0 && x <= 1000);
   ```

2. **Use helper functions** - Create helper functions for common patterns:
   ```java
   public static int nondetPositive() {
       int x = CProver.nondetInt();
       CProver.assume(x > 0);
       return x;
   }
   ```

3. **Add descriptive messages** - Include clear messages with assertions:
   ```java
   assert result >= 0 : "result must be non-negative";
   ```

4. **Separate verification from production** - Keep verification harnesses
   separate from production code

5. **Check satisfiability** - Ensure your assumptions are satisfiable (not
   contradictory)

## Further Reading

See the main documentation:
- [Java Modeling Constructs](../java-modeling-constructs.md) - Complete guide
- [JBMC User Manual](../jbmc-user-manual.md) - General JBMC usage
- [CBMC Tutorial](../cbmc-tutorial.md) - Basic tutorial

## Troubleshooting

### "Cannot execute CProver.XXX()" Runtime Error
This is expected! These examples are meant to be analyzed with JBMC, not
executed with regular Java.

### Verification Takes Too Long
Try:
- Reducing input ranges with tighter assumptions
- Using smaller unwind bounds for loops
- Simplifying the property being checked

### All Properties Pass Vacuously
Check that your assumptions are satisfiable. Contradictory assumptions will
cause all properties to pass vacuously.

## Contributing

If you have additional examples that would be helpful, please contribute them
following the existing style and structure.
