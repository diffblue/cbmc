public class Test_octal1
{
    public static void main()
    {
        String s = Integer.toString(-23, 8);
        assert(s.equals("-27"));
        assert(!s.equals("-27"));
    }
}
