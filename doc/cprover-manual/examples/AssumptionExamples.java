import org.cprover.CProver;

/**
 * Examples demonstrating the use of assumptions in JBMC
 */
public class AssumptionExamples {

    /**
     * Example 1: Basic assumption usage
     */
    public static void basicAssumption() {
        int x = CProver.nondetInt();

        // Restrict x to be in the range [1, 100]
        CProver.assume(x >= 1 && x <= 100);

        // Now JBMC will only consider values where 1 <= x <= 100
        assert x > 0 : "x is positive";     // This will succeed
        assert x <= 100 : "x is at most 100"; // This will succeed
    }

    /**
     * Example 2: Contrasting assumptions with assertions
     */
    public static void assumptionVsAssertion() {
        // INCORRECT approach - using assertion to constrain
        int x1 = CProver.nondetInt();
        // assert x1 > 0; // This would FAIL because x1 can be negative

        // CORRECT approach - using assumption to constrain
        int x2 = CProver.nondetInt();
        CProver.assume(x2 > 0);  // Only consider positive x2
        assert x2 > 0;           // This SUCCEEDS because x2 is constrained
    }

    /**
     * Example 3: Assumption ordering matters
     */
    public static void assumptionOrdering() {
        // WRONG: Assertion before assumption
        int x = CProver.nondetInt();
        // assert x == 100;  // This would fail
        // CProver.assume(x == 100);  // Too late!

        // CORRECT: Assumption before assertion
        int y = CProver.nondetInt();
        CProver.assume(y == 100);  // Constrain first
        assert y == 100;           // This succeeds
    }

    /**
     * Example 4: Constrained array access
     */
    public static void safeArrayAccess(int[] arr) {
        // Assume preconditions
        CProver.assume(arr != null);
        CProver.assume(arr.length > 0);

        int index = CProver.nondetInt();
        // Constrain index to valid range
        CProver.assume(index >= 0 && index < arr.length);

        // This access is now guaranteed to be safe
        int value = arr[index];
        assert value == arr[index]; // Trivially true, but demonstrates safety
    }

    /**
     * Example 5: Multiple constraints
     */
    public static void multipleConstraints() {
        int a = CProver.nondetInt();
        int b = CProver.nondetInt();

        // Apply multiple constraints
        CProver.assume(a >= 0);      // a is non-negative
        CProver.assume(b >= 0);      // b is non-negative
        CProver.assume(a <= 1000);   // a is bounded above
        CProver.assume(b <= 1000);   // b is bounded above
        CProver.assume(a != b);      // a and b are different

        // Now verify properties under these constraints
        assert a >= 0 && b >= 0 : "both values are non-negative";
        assert a != b : "values are different";
    }

    /**
     * Example 6: Modeling preconditions
     */
    public static int safeDivide(int numerator, int denominator) {
        return numerator / denominator;
    }

    public static void testSafeDivide() {
        int num = CProver.nondetInt();
        int den = CProver.nondetInt();

        // Model the precondition as an assumption
        CProver.assume(den != 0);  // Division by zero not allowed

        // Also prevent overflow
        CProver.assume(num >= -1000000 && num <= 1000000);
        CProver.assume(den >= -1000000 && den <= 1000000);

        int result = safeDivide(num, den);

        // Verify properties
        if (num == 0) {
            assert result == 0 : "zero divided by anything is zero";
        }
        if (den == 1) {
            assert result == num : "dividing by 1 gives original number";
        }
    }

    /**
     * Example 7: Modeling object properties
     */
    public static class Rectangle {
        int width, height;

        public Rectangle(int w, int h) {
            this.width = w;
            this.height = h;
        }

        public int area() {
            return width * height;
        }
    }

    public static void verifyRectangleArea() {
        int w = CProver.nondetInt();
        int h = CProver.nondetInt();

        // Assume valid dimensions
        CProver.assume(w > 0 && w <= 1000);
        CProver.assume(h > 0 && h <= 1000);

        Rectangle rect = new Rectangle(w, h);
        int area = rect.area();

        // Verify properties
        assert area > 0 : "area of valid rectangle is positive";
        assert area == w * h : "area calculation is correct";
        assert area >= w : "area is at least width";
        assert area >= h : "area is at least height";
    }

    /**
     * Example 8: Warning - Unsatisfiable assumptions
     */
    public static void unsatisfiableAssumptions() {
        int x = CProver.nondetInt();

        // These assumptions are contradictory!
        CProver.assume(x > 100);
        CProver.assume(x < 50);

        // This will "succeed" but vacuously - there are no valid inputs
        // assert false;  // Would incorrectly pass!

        // Better: Use satisfiable assumptions
        int y = CProver.nondetInt();
        CProver.assume(y > 50 && y < 100);
        assert y > 50 && y < 100; // Meaningful verification
    }

    /**
     * Example 9: Bounded input helpers
     */

    // Helper: Generate percentage (0-100)
    public static int nondetPercentage() {
        int percentage = CProver.nondetInt();
        CProver.assume(percentage >= 0 && percentage <= 100);
        return percentage;
    }

    // Helper: Generate positive integer
    public static int nondetPositive() {
        int value = CProver.nondetInt();
        CProver.assume(value > 0);
        return value;
    }

    public static void testBoundedHelpers() {
        int pct = nondetPercentage();
        assert pct >= 0 && pct <= 100 : "percentage is in valid range";

        int pos = nondetPositive();
        assert pos > 0 : "positive value is positive";
    }

    /**
     * Example 10: Complex constraints
     */
    public static void complexConstraints() {
        int[] arr = CProver.nondetWithoutNull(null);

        // Constrain array properties
        CProver.assume(arr.length >= 2 && arr.length <= 10);

        // Constrain array contents
        for (int i = 0; i < arr.length; i++) {
            CProver.assume(arr[i] >= 0 && arr[i] <= 100);
        }

        // Additional constraint: array is sorted
        for (int i = 1; i < arr.length; i++) {
            CProver.assume(arr[i] >= arr[i-1]);
        }

        // Now verify properties of sorted array
        assert arr[0] <= arr[arr.length - 1] : "first element <= last element";

        // Check any two adjacent elements
        int index = CProver.nondetInt();
        CProver.assume(index >= 0 && index < arr.length - 1);
        assert arr[index] <= arr[index + 1] : "array is sorted";
    }

    public static void main(String[] args) {
        // Run examples
        basicAssumption();
        assumptionVsAssertion();
        testSafeDivide();
        verifyRectangleArea();
        testBoundedHelpers();
        complexConstraints();
    }
}