public class Test_hex1
{
    public static void main()
    {
        String s = Integer.toString(-27, 16);
        assert(s.equals("-1b"));
        assert(!s.equals("-1b"));
    }
}
