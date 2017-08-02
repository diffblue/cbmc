public class Test_binary
{
    public static void main()
    {
        String s = Integer.toString(Integer.MIN_VALUE, 2);
        assert(s.equals("-10000000000000000000000000000000"));
        assert(!s.equals("-10000000000000000000000000000000"));
    }
}
