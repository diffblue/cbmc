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
        // 67_108_864 corresponds to the maximum length for which the solver
        // will concretize the string.
        if(s.length() <= 67_108_864 && t.length() <= 67_108_864)
            return;
        // Check at least one of them is short-ish, so we don't end up trying
        // to concretise a very long but *just* allowable string and memout the
        // test infrastructure:
        if(s.length() > 1024 && t.length() > 1024)
            return;
        if(CProverString.charAt(u, 2_000_000) != 'b')
            return;

        // Assert
        assert(false);
    }
}
