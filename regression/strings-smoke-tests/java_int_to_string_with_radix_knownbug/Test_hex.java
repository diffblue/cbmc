public class Test_hex
{
    public static void main()
    {
        String s = Integer.toString(Integer.MIN_VALUE, 16);
        assert(s.equals("-80000000"));
        assert(!s.equals("-80000000"));
    }
}
