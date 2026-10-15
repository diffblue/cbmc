[CPROVER Manual TOC](../)

## Fundamental Modeling Constructs for Java

This document explains how to use fundamental modeling constructs in Java when
working with JBMC (Java Bounded Model Checker). These constructs allow you to
write verification harnesses and specify properties that JBMC will check
exhaustively.

### Table of Contents

1. [Assertions](#assertions)
2. [Non-determinism](#non-determinism)
3. [Assumptions](#assumptions)
4. [Complete Example](#complete-example)

---

## Assertions

Assertions are used to specify properties that should hold in your program.
JBMC will verify that these properties are true for all possible program
executions.

### Using Java's Standard `assert` Keyword

The simplest way to specify properties is using Java's built-in `assert`
statement:

```java
public class AssertExample {
    public static void checkPositive(int x) {
        assert x > 0 : "x must be positive";
    }
}
```

When JBMC analyzes this code, it will verify that the assertion holds for all
possible values of `x`. If the assertion can be violated, JBMC will report a
failure and provide a counterexample.

**Key Points:**
- The assertion message (after the colon) is optional but recommended for
  clarity
- JBMC checks assertions statically for **all** possible inputs
- Unlike runtime assertion checking, JBMC does not require the `-ea` flag

### Example: Array Bounds Safety

```java
public class ArrayExample {
    public static void accessArray(int[] arr, int index) {
        // JBMC automatically checks array bounds, but you can add explicit
        // assertions for clarity
        assert index >= 0 && index < arr.length : "index is within bounds";
        int value = arr[index];
        assert value >= 0 : "array contains non-negative values";
    }
}
```

---

## Non-determinism

Non-determinism allows you to model arbitrary or unknown input values. This is
essential for verification because it enables JBMC to check your code against
**all possible inputs**, not just specific test cases.

### The `org.cprover.CProver` Class

JBMC provides the `org.cprover.CProver` class with methods for generating
non-deterministic values. These methods return arbitrary values of their
respective types.

The API's source of truth is the
[java-cprover-api](https://github.com/diffblue/java-cprover-api) project,
distributed as `cprover-api.jar`. To compile code that uses it, put that jar on
the classpath -- do not copy the class into your project. (In the CBMC source
tree the jar is built from the `java-models-library` submodule at
`jbmc/lib/java-models-library/target/cprover-api.jar`.)

### Primitive Type Non-determinism

The following methods are available for primitive types:

```java
import org.cprover.CProver;

public class NondetExample {
    public static void demonstrateNondet() {
        // Generate non-deterministic primitive values
        boolean b = CProver.nondetBoolean();  // arbitrary boolean
        byte    by = CProver.nondetByte();     // arbitrary byte
        char    c = CProver.nondetChar();      // arbitrary char
        short   s = CProver.nondetShort();     // arbitrary short
        int     i = CProver.nondetInt();       // arbitrary int
        long    l = CProver.nondetLong();      // arbitrary long
        float   f = CProver.nondetFloat();     // arbitrary float
        double  d = CProver.nondetDouble();    // arbitrary double
    }
}
```

**Important Notes:**
- These methods have no implementation body - they are recognized and handled
  specially by JBMC
- Non-deterministic values represent **all possible** values of that type
- Non-determinism is **not** the same as randomness; it's universal
  quantification over all possible values

### Object Non-determinism

For reference types (objects), JBMC provides two methods:

```java
import org.cprover.CProver;

public class ObjectNondetExample {
    public static void demonstrateObjectNondet() {
        // Non-deterministic object that CAN be null
        String s1 = CProver.nondetWithNull(null);
        // s1 might be null or might be a valid String object

        // Non-deterministic object that CANNOT be null
        String s2 = CProver.nondetWithoutNull(null);
        // s2 is guaranteed to be a valid String object (not null)
    }
}
```

**Key Differences:**
- `nondetWithNull(null)` - returns an arbitrary object that may or may not be
  null
- `nondetWithoutNull(null)` - returns an arbitrary object that is guaranteed to
  be non-null

Both are generic (`<T> T nondetWithNull(T)`); the argument is only a type
template, so pass `null` and let the result type be inferred from the
assignment (e.g. `String s = CProver.nondetWithNull(null);`).

### Practical Example: Verifying a Division Function

```java
import org.cprover.CProver;

public class DivisionExample {
    public static int safeDivide(int numerator, int denominator) {
        if (denominator == 0) {
            return 0; // or throw an exception
        }
        return numerator / denominator;
    }

    public static void verifyDivision() {
        // Generate arbitrary inputs
        int a = CProver.nondetInt();
        int b = CProver.nondetInt();

        // Call the function
        int result = safeDivide(a, b);

        // Verify properties
        if (b != 0) {
            assert result == a / b : "division is correct";
        } else {
            assert result == 0 : "division by zero returns 0";
        }
    }
}
```

---

## Assumptions

Assumptions are used to restrict the search space by constraining non-deterministic
inputs. They tell JBMC: "only consider program executions where this condition
holds."

### The `CProver.assume()` Method

```java
import org.cprover.CProver;

public class AssumeExample {
    public static void demonstrateAssume() {
        int x = CProver.nondetInt();

        // Restrict x to be in the range [1, 100]
        CProver.assume(x >= 1 && x <= 100);

        // Now JBMC will only consider values where 1 <= x <= 100
        assert x > 0 : "x is positive";  // This will succeed
        assert x <= 100 : "x is at most 100";  // This will succeed
    }
}
```

### Assumptions vs. Assertions

It's crucial to understand the difference:

- **Assertion**: "I claim this property MUST hold"
  - If violated, JBMC reports a verification failure
  - Used to specify **what you want to prove**

- **Assumption**: "Only consider cases where this holds"
  - Cannot be violated - constrains the search space
  - Used to specify **preconditions** or **input constraints**

### Example: Comparing Assumptions and Assertions

```java
import org.cprover.CProver;

public class AssumeVsAssert {
    // INCORRECT: This will fail
    public static void incorrectUse() {
        int x = CProver.nondetInt();
        assert x > 0;  // FAILS: x can be negative or zero
    }

    // CORRECT: Use assume to constrain the input
    public static void correctUse() {
        int x = CProver.nondetInt();
        CProver.assume(x > 0);  // Only consider positive x
        assert x > 0;  // SUCCEEDS: x is constrained to be positive
    }
}
```

### Warning: Ensure Assumptions are Satisfiable

Always ensure your assumptions can be satisfied. Unsatisfiable assumptions lead
to vacuous verification:

```java
import org.cprover.CProver;

public class UnsatisfiableExample {
    public static void vacuousVerification() {
        int x = CProver.nondetInt();

        // These assumptions are contradictory!
        CProver.assume(x > 100);
        CProver.assume(x < 50);

        // This will "succeed" but vacuously - there are no valid inputs
        assert false;  // Incorrectly passes!
    }
}
```

### Assumptions are Non-Retroactive

Assumptions only affect assertions that follow them in program order:

```java
import org.cprover.CProver;

public class AssumptionOrderExample {
    // INCORRECT: Assumption comes after assertion
    public static void wrongOrder() {
        int x = CProver.nondetInt();
        assert x == 100;  // FAILS: x is not constrained yet
        CProver.assume(x == 100);  // Too late!
    }

    // CORRECT: Assumption comes before assertion
    public static void correctOrder() {
        int x = CProver.nondetInt();
        CProver.assume(x == 100);  // Constrain first
        assert x == 100;  // SUCCEEDS: x is now constrained
    }
}
```

### Practical Example: Constrained Array Access

```java
import org.cprover.CProver;

public class ArrayAccessExample {
    public static void safeArrayAccess(int[] arr) {
        // Assume arr is non-null and has at least one element
        CProver.assume(arr != null);
        CProver.assume(arr.length > 0);

        int index = CProver.nondetInt();
        // Constrain index to valid range
        CProver.assume(index >= 0 && index < arr.length);

        // This access is now guaranteed to be safe
        int value = arr[index];
        assert value == arr[index];  // Trivially true, but demonstrates safety
    }
}
```

### Common Pattern: Modeling Bounded Inputs

A common use case is to model inputs within specific ranges:

```java
import org.cprover.CProver;

public class BoundedInputExample {
    // Model a percentage (0-100)
    public static int nondetPercentage() {
        int percentage = CProver.nondetInt();
        CProver.assume(percentage >= 0 && percentage <= 100);
        return percentage;
    }

    // Model a positive integer
    public static int nondetPositive() {
        int value = CProver.nondetInt();
        CProver.assume(value > 0);
        return value;
    }

    public static void useConstrainedInputs() {
        int pct = nondetPercentage();
        assert pct >= 0 && pct <= 100;  // Always succeeds

        int pos = nondetPositive();
        assert pos > 0;  // Always succeeds
    }
}
```

---

## Complete Example

Here's a complete example that demonstrates all three concepts together. The
full, runnable program is the canonical
[`examples/BankingExample.java`](https://raw.githubusercontent.com/diffblue/cbmc/develop/doc/cprover-manual/examples/BankingExample.java);
the excerpt below shows its verification harness, which combines
non-determinism, assumptions and assertions:

```java
public static void verifyTransfer() {
    // 1. NON-DETERMINISM: create arbitrary inputs
    int fromBalance = CProver.nondetInt();
    int amount = CProver.nondetInt();

    // 2. ASSUMPTIONS: constrain inputs to valid ranges
    CProver.assume(fromBalance >= 0);
    CProver.assume(amount >= 0 && amount <= 1000000);

    // Call the function under test
    boolean result = transfer(fromBalance, amount);

    // 3. ASSERTIONS: verify expected properties
    if (amount <= 0) {
        assert !result : "transfer should fail for non-positive amount";
    }
    if (amount > 0 && fromBalance < amount) {
        assert !result : "transfer should fail for insufficient funds";
    }
    if (amount > 0 && fromBalance >= amount) {
        assert result : "transfer should succeed when funds are sufficient";
    }
}
```

The companion `verifyWithObjects()` harness (see the full file) additionally
demonstrates object non-determinism with a possibly-null `String`.

### Running JBMC on This Example

To verify this example with JBMC:

1. Compile the Java file against the CProver API (`cprover-api.jar`, see
   [The `org.cprover.CProver` Class](#the-orgcprovercprover-class) above):
   ```bash
   javac -cp /path/to/cprover-api.jar BankingExample.java
   ```

2. Run JBMC. Because `verifyWithObjects()` exercises `java.lang.String`
   (`message.length()`), the core models must be on the classpath (see the
   [JBMC User Manual](../jbmc-user-manual/) under "Java Library support"):
   ```bash
   jbmc BankingExample \
     --cp <CBMC>/jbmc/src/java_bytecode/library/core-models.jar:.
   ```

3. JBMC will exhaustively check all assertions for all possible input
   combinations (subject to the assumptions).

---

## Best Practices

### 1. Use Descriptive Assertion Messages

```java
// Good
assert balance >= 0 : "account balance must be non-negative";

// Less helpful
assert balance >= 0;
```

### 2. Constrain Non-deterministic Inputs Appropriately

```java
// Too loose - may cause state explosion
int x = CProver.nondetInt();

// Better - constrain to relevant range
int x = CProver.nondetInt();
CProver.assume(x >= 0 && x <= 100);
```

### 3. Separate Test Logic from Production Code

Keep your verification harnesses separate from production code:

```java
// Production code
public class Calculator {
    public static int add(int a, int b) {
        return a + b;
    }
}

// Verification harness (separate file or test method)
public class CalculatorVerification {
    public static void verifyAdd() {
        int a = CProver.nondetInt();
        int b = CProver.nondetInt();
        // Add reasonable bounds
        CProver.assume(a >= -1000 && a <= 1000);
        CProver.assume(b >= -1000 && b <= 1000);

        int result = Calculator.add(a, b);
        assert result == a + b;
    }
}
```

### 4. Be Aware of State Space Explosion

The number of states JBMC explores grows with:
- Number of non-deterministic choices
- Loop iterations
- Recursion depth
- Object complexity

Use assumptions to keep the state space manageable.

---

## Common Pitfalls

### 1. Forgetting to Import CProver

```java
// ERROR: CProver not imported
public class Example {
    public static void test() {
        int x = CProver.nondetInt();  // Compilation error!
    }
}

// CORRECT: Import the class
import org.cprover.CProver;

public class Example {
    public static void test() {
        int x = CProver.nondetInt();  // OK
    }
}
```

### 2. Using Assumptions Instead of Assertions

```java
// WRONG: Using assume to check a property
public static void incorrectCheck(int x) {
    CProver.assume(x > 0);  // This doesn't check anything!
}

// CORRECT: Use assert to check properties
public static void correctCheck(int x) {
    assert x > 0 : "x must be positive";  // This checks the property
}
```

### 3. Creating Unsatisfiable Assumptions

```java
// WRONG: Contradictory assumptions
int x = CProver.nondetInt();
CProver.assume(x > 100);
CProver.assume(x < 0);
// No value of x can satisfy both constraints!
```

---

## Further Reading

- [JBMC User Manual](../jbmc-user-manual/) - General JBMC usage
- [Modeling with Assumptions (C)](../modeling/assumptions/) - C language assumptions
- [Nondeterminism (C)](../modeling/nondeterminism/) - C language nondeterminism
- [CBMC Tutorial](../cbmc/tutorial/) - Basic CBMC/JBMC tutorial

### Runnable Examples

The complete, runnable versions of the programs used throughout this guide live
in the
[`examples/`](https://github.com/diffblue/cbmc/tree/develop/doc/cprover-manual/examples)
directory. These are the canonical sources (the snippets above are excerpts of
them). See
[`examples/QuickReference.md`](https://github.com/diffblue/cbmc/blob/develop/doc/cprover-manual/examples/QuickReference.md)
for a condensed cheat-sheet and
[`examples/README.md`](https://github.com/diffblue/cbmc/blob/develop/doc/cprover-manual/examples/README.md)
for build and JBMC run instructions.

---

## Summary

| Construct | Purpose | Example |
|-----------|---------|---------|
| **Assertion** | Specify properties to verify | `assert x > 0 : "x is positive";` |
| **Non-determinism** | Model arbitrary inputs | `int x = CProver.nondetInt();` |
| **Assumption** | Constrain input space | `CProver.assume(x > 0 && x < 100);` |

Remember:
- **Assert** what you want to **prove**
- **Assume** what you want to **constrain**
- Use **non-determinism** to represent **arbitrary inputs**

These three constructs form the foundation of writing effective verification
harnesses for JBMC.
