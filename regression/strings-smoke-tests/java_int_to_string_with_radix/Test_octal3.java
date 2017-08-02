public class Test_octal3
{
    public static void main()
    {
        String s = Integer.toString(Integer.MIN_VALUE + 1, 8);
        assert(s.equals("-17777777777"));
        assert(!s.equals("-17777777777"));
    }
}
