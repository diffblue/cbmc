// Uses CProverString, must be compiled with ../cprover/CProverString.java
import org.cprover.*;

public class Test {
    public static void check(int i, String s) {
        String t = "Hello World";
        Integer x = new Integer(2);
        if (i==0)
            assert("Hello World".equals(t));
        else if (i==1)
            assert(! "Hello World".equals(s));
        else if (i==2)
            assert(! "Hello World".equals(x));
        else if (i==3)
            assert("Hello World".equals(x));
        else if (i==4)
            assert(! s.equals(x));
        else if (i==5)
            assert(s.equals(x));
    }

    public static boolean referenceImplementation(String s, Object o) {
        if (! (o instanceof String))
            return false;

        String s2 = (String) o;
        if (s.length() != s2.length())
            return false;

        for (int i = 0; i < s.length(); i++) {
            if (CProverString.charAt(s, i) != CProverString.charAt(s2, i))
                return false;
        }

        return true;
    }

    public static boolean verifyNonNull(String s, Object o) {
        // Filter
        if (s == null || o == null)
            return false;

        // Act
        boolean result = s.equals(o);
        boolean referenceResult = referenceImplementation(s, o);

        // Assert
        assert result == referenceResult;

        // Return
        return result;
    }

    public static boolean verify(String s, Object o) {
        // Act
        boolean result = s.equals(o);
        boolean referenceResult = referenceImplementation(s, o);

        // Assert
        assert result == referenceResult;

        // Return
        return result;
    }

}
