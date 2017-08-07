public class Test_binary3
{
    public static void main()
    {
        String s = Integer.toString(Integer.MIN_VALUE + 1, 2);
        assert(s.equals("-1111111111111111111111111111111"));
        assert(!s.equals("-1111111111111111111111111111111"));
    }
}
