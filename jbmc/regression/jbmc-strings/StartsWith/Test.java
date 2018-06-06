// Must be compiled with CProverString:
// javac Test.java ../cprover/CProverString.java
public class Test {

    // Reference implementation
    public static boolean referenceStartsWith(String s, String prefix, int offset) {
        if (offset < 0 || offset > s.length() - prefix.length()) {
            return false;
        }

        for (int i = 0; i < prefix.length(); i++) {
            if (org.cprover.CProverString.charAt(s, offset + i)
                    != org.cprover.CProverString.charAt(prefix, i)) {
                return false;
            }
        }
        return true;
    }

    public static boolean check(String s, String t, int offset) {
        // Filter out null strings
        if(s == null || t == null) {
            return false;
        }

        // Act
        final boolean result = s.startsWith(t, offset);

        // Assert
        final boolean referenceResult = referenceStartsWith(s, t, offset);
        assert(result == referenceResult);

        // Check reachability
        assert(result == false);
        return result;
    }

    public static boolean checkDet() {
        boolean result = false;
        result = "foo".startsWith("foo", 0);
        assert(result);
        result = "foo".startsWith("f", -1);
        assert(!result);
        result = "foo".startsWith("oo", 1);
        assert(result);
        result = "foo".startsWith("f", 1);
        assert(!result);
        result = "foo".startsWith("bar", 0);
        assert(!result);
        result = "foo".startsWith("oo", 2);
        assert(!result);
        assert(false);
        return result;
    }

    public static boolean checkNonDet(String s) {
        // Filter
        if (s == null) {
            return false;
        }

        // Act
        final boolean result = s.startsWith(s, 1);

        // Assert
        assert(!result);

        // Check reachability
        assert(false);
        return result;
    }
}
