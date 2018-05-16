public class Test {

    public static String check(String t) {
        String s = t.concat("$£¥\u0000\u0008\u0010\u001F");
        // This should be disallowed because "\u0000" is not printable
        assert(!s.equals("\u0000$£¥\u0000\u0008\u0010\u001F"));
        // This can fail when t="a" which is printable
        assert(!s.equals("a$£¥\u0000\u0008\u0010\u001F"));
        return s;
    }

    public static boolean check_char(String s, char c) {
        if(s == null)
            return false;
        // This should be -1 for all non-printable character
        int i = s.indexOf(c);
        boolean b = (i == -1 || (c >= ' ' && c <= '~'));
        assert(b);
        return b;
    }
}
