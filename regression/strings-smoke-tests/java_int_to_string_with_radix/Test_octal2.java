public class Test_octal2
{
    public static void main()
    {
        String s = Integer.toString(Integer.MAX_VALUE, 8);
        assert(s.equals("17777777777"));
        assert(!s.equals("17777777777"));
    }
}
