public class Test_hex3
{
    public static void main()
    {
        String s = Integer.toString(Integer.MIN_VALUE + 1, 16);
        assert(s.equals("-7fffffff"));
        assert(!s.equals("-7fffffff"));
    }
}
