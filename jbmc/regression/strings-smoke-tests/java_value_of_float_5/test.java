public class test
{
    public static void check()
    {
        String s1=String.valueOf(-123.456f);
        assert(s1.equals("-123.456"));
        assert(!s1.equals("-123.456"));
    }
}
