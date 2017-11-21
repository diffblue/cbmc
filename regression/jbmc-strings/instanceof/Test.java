public class Test {

    public static String check(String s) {
        if (s == null)
            return "null";
        assert(s instanceof String);
        return "non-null";
    }
}
