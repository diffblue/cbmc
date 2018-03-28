public class Test {
    public static int check(int i) {
        String s = "\u0000";

        if (i == 0)
            assert(s.length() == 1);
        else if (i == 1)
            assert(s.length() != 1);

        return s.length();
    }
}
