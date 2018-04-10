import org.cprover.CProverString;

public class Test {
    public static void check(String s, String t) {
        // Filter
        if(s == null || t == null)
            return;

        // Act
        String u = s.concat(t);

        // Filter out
        if(u.length() < 3_000_000)
            return;
        if(CProverString.charAt(u, 500_000) != 'a')
            return;
        if(CProverString.charAt(u, 2_000_000) != 'b')
            return;

        // Assert
        assert(false);
    }

    public static void checkAbort(String s, String t) {
        // Filter
        if(s == null || t == null)
            return;

        // Act
        String u = s.concat(t);

        // Filter out
        if(u.length() < 67_108_864)
            return;
        if(CProverString.charAt(u, 2_000_000) != 'b')
            return;

        // Assert
        assert(false);
    }
}
