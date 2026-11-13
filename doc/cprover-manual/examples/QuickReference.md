# JBMC Java Modeling Constructs - Quick Reference

This is a quick reference guide for using fundamental modeling constructs in
JBMC. For detailed explanations and examples, see the
[full documentation](../java-modeling-constructs.md).

## Import Statement

```java
import org.cprover.CProver;
```

`org.cprover.CProver` comes from
[java-cprover-api](https://github.com/diffblue/java-cprover-api)
(`cprover-api.jar`); put that jar on the classpath to compile.

---

## Assertions

### Standard Java Assertions

```java
assert condition : "optional message";
```

**Example:**
```java
assert x > 0 : "x must be positive";
assert arr.length > 0 : "array must not be empty";
```

**Purpose:** Specify properties that JBMC should verify hold for all inputs.

---

## Non-deterministic Values

### Primitive Types

| Method | Returns | Description |
|--------|---------|-------------|
| `CProver.nondetBoolean()` | `boolean` | Arbitrary boolean value |
| `CProver.nondetByte()` | `byte` | Arbitrary byte value |
| `CProver.nondetChar()` | `char` | Arbitrary char value |
| `CProver.nondetShort()` | `short` | Arbitrary short value |
| `CProver.nondetInt()` | `int` | Arbitrary int value |
| `CProver.nondetLong()` | `long` | Arbitrary long value |
| `CProver.nondetFloat()` | `float` | Arbitrary float value |
| `CProver.nondetDouble()` | `double` | Arbitrary double value |

**Example:**
```java
int x = CProver.nondetInt();     // x can be any integer
boolean b = CProver.nondetBoolean();  // b can be true or false
```

### Object Types

| Method | Returns | Null Possible? |
|--------|---------|----------------|
| `CProver.nondetWithNull(null)` | `<T>` | Yes - may be null |
| `CProver.nondetWithoutNull(null)` | `<T>` | No - never null |

**Example:**
```java
String s1 = CProver.nondetWithNull(null);      // might be null
String s2 = CProver.nondetWithoutNull(null);   // guaranteed non-null
```

**Purpose:** Model arbitrary/unknown input values for exhaustive verification.

---

## Assumptions

### Basic Usage

```java
CProver.assume(condition);
```

**Purpose:** Constrain the search space by restricting which inputs to consider.

### Common Patterns

**Range constraint:**
```java
int x = CProver.nondetInt();
CProver.assume(x >= 0 && x <= 100);  // Only consider 0 <= x <= 100
```

**Non-null constraint:**
```java
String s = CProver.nondetWithNull(null);
CProver.assume(s != null);  // Only consider non-null strings
```

**Array constraints:**
```java
int[] arr = CProver.nondetWithNull(null);
CProver.assume(arr != null);
CProver.assume(arr.length > 0 && arr.length <= 10);
```

**Multiple constraints:**
```java
int a = CProver.nondetInt();
int b = CProver.nondetInt();
CProver.assume(a > 0);
CProver.assume(b > 0);
CProver.assume(a < b);  // a is positive and less than b
```

---

## Key Differences

### Assertion vs. Assumption

| Aspect | Assertion (`assert`) | Assumption (`CProver.assume()`) |
|--------|---------------------|--------------------------------|
| **Purpose** | Check a property | Constrain inputs |
| **When false** | Verification FAILS | Input is ignored |
| **Use for** | What you want to PROVE | What you want to ASSUME |

**Example:**
```java
// WRONG: Using assert to constrain
int x = CProver.nondetInt();
assert x > 0;  // FAILS! x can be <= 0

// CORRECT: Use assume to constrain, assert to verify
int x = CProver.nondetInt();
CProver.assume(x > 0);  // Constrain to positive
assert x > 0;           // SUCCEEDS - x is positive
```

---

## Complete Verification Harness Pattern

```java
import org.cprover.CProver;

public class MyVerification {

    // Function to verify
    public static boolean myFunction(int input) {
        if (input < 0) return false;
        // ... more logic ...
        return true;
    }

    // Verification harness
    public static void verifyMyFunction() {
        // 1. Generate non-deterministic input
        int input = CProver.nondetInt();

        // 2. Constrain input to relevant range
        CProver.assume(input >= -1000 && input <= 1000);

        // 3. Call function
        boolean result = myFunction(input);

        // 4. Assert expected properties
        if (input < 0) {
            assert !result : "negative input returns false";
        } else {
            // assert other properties...
        }
    }
}
```

---

## Running JBMC

### Basic Command

```bash
jbmc MyClass --function MyClass.verifyMethod
```

### Common Options

```bash
# Show trace on failure
jbmc MyClass --function MyClass.verify --trace

# Set loop unwind bound
jbmc MyClass --function MyClass.verify --unwind 10

# Enable runtime exceptions
jbmc MyClass --function MyClass.verify --throw-runtime-exceptions

# Multiple options
jbmc MyClass \
  --function MyClass.verify \
  --unwind 20 \
  --trace \
  --throw-runtime-exceptions
```

---

## Helper Functions Pattern

Create helper functions for common input patterns:

```java
// Generate percentage (0-100)
public static int nondetPercentage() {
    int x = CProver.nondetInt();
    CProver.assume(x >= 0 && x <= 100);
    return x;
}

// Generate positive integer
public static int nondetPositive() {
    int x = CProver.nondetInt();
    CProver.assume(x > 0);
    return x;
}

// Generate non-null array with size constraint
public static int[] nondetArray(int minSize, int maxSize) {
    int[] arr = CProver.nondetWithoutNull(null);
    CProver.assume(arr.length >= minSize && arr.length <= maxSize);
    return arr;
}
```

---

## Common Pitfalls

### ❌ Don't: Use assertion to constrain input
```java
int x = CProver.nondetInt();
assert x > 0;  // WRONG! This will fail
```

### ✅ Do: Use assumption to constrain input
```java
int x = CProver.nondetInt();
CProver.assume(x > 0);  // CORRECT
assert x > 0;  // Now this succeeds
```

---

### ❌ Don't: Assume after assert
```java
int x = CProver.nondetInt();
assert x == 100;         // WRONG! Too early
CProver.assume(x == 100); // Too late
```

### ✅ Do: Assume before assert
```java
int x = CProver.nondetInt();
CProver.assume(x == 100);  // Constrain first
assert x == 100;           // Then verify
```

---

### ❌ Don't: Create unsatisfiable assumptions
```java
int x = CProver.nondetInt();
CProver.assume(x > 100);
CProver.assume(x < 50);  // WRONG! Contradictory
// All assertions will pass vacuously!
```

### ✅ Do: Ensure assumptions are satisfiable
```java
int x = CProver.nondetInt();
CProver.assume(x > 50 && x < 100);  // CORRECT - satisfiable
```

---

## Cheat Sheet

```java
import org.cprover.CProver;

// Non-determinism - create arbitrary values
int x = CProver.nondetInt();
String s = CProver.nondetWithNull(null);

// Assumptions - constrain inputs
CProver.assume(x > 0 && x < 100);
CProver.assume(s != null);

// Assertions - verify properties
assert x > 0 : "x is positive";
assert s.length() >= 0 : "length is non-negative";
```

---

## More Information

- [Full Documentation](../java-modeling-constructs.md)
- [Examples Directory](.)
- [JBMC User Manual](../jbmc-user-manual.md)
