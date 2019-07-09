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

    public static boolean printable_char(char c) {
      boolean b = c >= ' ' && c <= '~';
      assert(b);
      return b;
    }

    public char charField;

    public boolean test_char_field() {
      boolean b = charField >= ' ' && charField <= '~';
      assert(b);
      return b;
    }

    public static boolean printable_char_array(char[] c) {
      if(c.length != 3 || c == null)
        return false;
      boolean b0 = c[0] >= ' ' && c[0] <= '~';
      boolean b1 = c[1] >= ' ' && c[1] <= '~';
      boolean b2 = c[2] >= ' ' && c[2] <= '~';
      assert(b0 || b1 || b2);
      return b0 || b1 || b2;
    }

    public static char charStaticField = 'a';

     public boolean test_char_field_static() {
      if(charStaticField == 'a')
        return false;
      boolean b = charStaticField >= ' ' && charStaticField <= '~';
      assert(b);
      return b;
    }

}
