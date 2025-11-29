import org.cprover.CProver;

/**
 * Examples demonstrating non-determinism in JBMC
 */
public class NondeterminismExamples {

    /**
     * Example 1: All primitive type non-deterministic values
     */
    public static void allPrimitiveTypes() {
        // Generate non-deterministic primitive values
        boolean b = CProver.nondetBoolean();  // arbitrary boolean
        byte    by = CProver.nondetByte();    // arbitrary byte
        char    c = CProver.nondetChar();     // arbitrary char
        short   s = CProver.nondetShort();    // arbitrary short
        int     i = CProver.nondetInt();      // arbitrary int
        long    l = CProver.nondetLong();     // arbitrary long
        float   f = CProver.nondetFloat();    // arbitrary float
        double  d = CProver.nondetDouble();   // arbitrary double

        // These values can be anything within their type's range
        System.out.println("Non-deterministic values generated");
    }

    /**
     * Example 2: Non-deterministic object with null
     */
    public static void nondetWithNull() {
        // This string might be null or a valid String
        String s = CProver.nondetWithNull(null);

        if (s != null) {
            int length = s.length();
            assert length >= 0 : "string length is non-negative";
        } else {
            // Handle the null case
            System.out.println("String is null");
        }
    }

    /**
     * Example 3: Non-deterministic object without null
     */
    public static void nondetWithoutNull() {
        // This string is guaranteed to be non-null
        String s = CProver.nondetWithoutNull(null);

        // No null check needed!
        int length = s.length();
        assert length >= 0 : "string length is non-negative";
    }

    /**
     * Example 4: Verifying a function with arbitrary inputs
     */
    public static int absolute(int x) {
        if (x < 0) {
            return -x;
        }
        return x;
    }

    public static void verifyAbsolute() {
        // Test with arbitrary input
        int x = CProver.nondetInt();

        // Constrain to prevent overflow
        CProver.assume(x != Integer.MIN_VALUE);

        int result = absolute(x);

        // Verify the result is always non-negative
        assert result >= 0 : "absolute value is non-negative";

        // Verify the result has correct magnitude
        if (x >= 0) {
            assert result == x : "absolute of positive is itself";
        } else {
            assert result == -x : "absolute of negative is negation";
        }
    }

    /**
     * Example 5: Using non-determinism to find edge cases
     */
    public static boolean isPrime(int n) {
        if (n <= 1) return false;
        if (n == 2) return true;
        if (n % 2 == 0) return false;

        for (int i = 3; i * i <= n; i += 2) {
            if (n % i == 0) return false;
        }
        return true;
    }

    public static void testPrimeCounter() {
        int n = CProver.nondetInt();

        // Only test in a reasonable range
        CProver.assume(n >= 1 && n <= 100);

        boolean result = isPrime(n);

        // Verify known primes
        if (n == 2 || n == 3 || n == 5 || n == 7) {
            assert result : "small primes are correctly identified";
        }

        // Verify known composites
        if (n == 4 || n == 6 || n == 8 || n == 9) {
            assert !result : "small composites are correctly identified";
        }
    }

    /**
     * Example 6: Modeling input with specific characteristics
     */
    public static class Person {
        String name;
        int age;

        public Person(String name, int age) {
            this.name = name;
            this.age = age;
        }
    }

    public static boolean isAdult(Person p) {
        return p.age >= 18;
    }

    public static void verifyIsAdult() {
        // Create a person with non-deterministic age
        int age = CProver.nondetInt();
        CProver.assume(age >= 0 && age <= 150); // Reasonable age range

        String name = CProver.nondetWithoutNull(null);
        Person p = new Person(name, age);

        boolean result = isAdult(p);

        // Verify the classification
        if (age >= 18) {
            assert result : "person aged 18+ is an adult";
        } else {
            assert !result : "person under 18 is not an adult";
        }
    }

    /**
     * Example 7: Finding counterexamples
     */
    public static void findCounterexample() {
        int x = CProver.nondetInt();
        int y = CProver.nondetInt();

        // Constrain to small values
        CProver.assume(x >= 0 && x <= 10);
        CProver.assume(y >= 0 && y <= 10);

        // This assertion is false - JBMC will find a counterexample
        // (try running to see what values it finds!)
        // assert x + y != 10 : "sum is never 10";

        // This assertion is true
        assert x + y >= 0 : "sum is non-negative";
    }

    public static void main(String[] args) {
        // Run verifications
        verifyAbsolute();
        testPrimeCounter();
        verifyIsAdult();
        findCounterexample();
    }
}
