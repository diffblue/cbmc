public class Test_octal
{
    public static void main()
    {
        String s = Integer.toString(Integer.MIN_VALUE, 8);
        assert(s.equals("-20000000000"));
        assert(!s.equals("-20000000000"));
    }
}
