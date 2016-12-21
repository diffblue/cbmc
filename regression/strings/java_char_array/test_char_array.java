public class test_char_array {

    public static void main(String[] argv)
    {
        String s = "abc";
        char [] str = s.toCharArray();
        int[] test = new int[312];
        char c = str[2];
        String t = argv[0];
        char d = t.charAt(0);
        assert(str.length == 3);
        assert(c == 'c');
        assert(c == d || d < 'a' || d > 'z' );
    }
}
