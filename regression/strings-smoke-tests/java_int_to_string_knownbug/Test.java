public class Test
{
    public static void main()
    {
        String t = Integer.toString(Integer.MIN_VALUE);
        assert(t.equals("-2147483648"));
        assert(!t.equals("-2147483648"));
    }
}
