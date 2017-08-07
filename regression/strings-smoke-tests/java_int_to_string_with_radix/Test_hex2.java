public class Test_hex2
{
    public static void main()
    {
        String s = Integer.toString(Integer.MAX_VALUE, 16);
        assert(s.equals("7fffffff"));
        assert(!s.equals("7fffffff"));
    }
}
