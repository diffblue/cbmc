public class Test {
    public static String check(String s) {
        // Filter
        if (s == null) {
            return "Null string";
        }
        if (s.length() < 16_000_000) {
            return "Too short";
        }

        // Act
        boolean b1 = s.contains("foobar");

        // Filter output
        if (b1) {
            return "Contained";
        }

        // Assert
        assert(false);
        return "Unreachable";
    }
}
