public class Test_decimal
{
    public static void main()
    {
        String s = Integer.toString(-27, 10);
        assert(s.equals("-27"));
        assert(!s.equals("-27"));
    }
}
