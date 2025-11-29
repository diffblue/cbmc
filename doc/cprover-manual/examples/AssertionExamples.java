import org.cprover.CProver;

/**
 * Examples demonstrating various assertion patterns in JBMC
 */
public class AssertionExamples {

    /**
     * Example 1: Basic assertion
     */
    public static void basicAssertion(int x) {
        assert x > 0 : "x must be positive";
    }

    /**
     * Example 2: Array bounds safety
     */
    public static void arrayBoundsSafety(int[] arr, int index) {
        // Explicitly assert bounds (JBMC also checks this automatically)
        assert arr != null : "array must not be null";
        assert index >= 0 && index < arr.length : "index must be within bounds";

        int value = arr[index];
        assert value >= 0 : "array contains non-negative values";
    }

    /**
     * Example 3: Verifying mathematical properties
     */
    public static void mathematicalProperties() {
        int a = CProver.nondetInt();
        int b = CProver.nondetInt();

        // Constrain inputs to prevent overflow
        CProver.assume(a >= -1000 && a <= 1000);
        CProver.assume(b >= -1000 && b <= 1000);

        // Verify commutativity of addition
        assert a + b == b + a : "addition is commutative";

        // Verify associativity (when no overflow occurs)
        int c = CProver.nondetInt();
        CProver.assume(c >= -1000 && c <= 1000);
        assert (a + b) + c == a + (b + c) : "addition is associative";
    }

    /**
     * Example 4: Verifying all array elements
     */
    public static void verifyAllElements(int[] arr) {
        CProver.assume(arr != null);
        CProver.assume(arr.length > 0 && arr.length <= 10);

        // Initialize all elements to zero
        for (int i = 0; i < arr.length; i++) {
            arr[i] = 0;
        }

        // Use non-determinism to check all elements
        int index = CProver.nondetInt();
        CProver.assume(index >= 0 && index < arr.length);

        // This assertion checks that ALL elements are zero
        assert arr[index] == 0 : "all array elements are zero";
    }

    /**
     * Example 5: Pre and postconditions
     */
    public static int divide(int numerator, int denominator) {
        // Precondition
        assert denominator != 0 : "denominator must not be zero";

        int result = numerator / denominator;

        // Postcondition
        assert numerator == result * denominator + numerator % denominator :
               "division identity: numerator == quotient * denominator + remainder";

        return result;
    }

    public static void main(String[] args) {
        // These would be run by JBMC
        mathematicalProperties();
    }
}
