public class Test_binary2
{
    public static void main()
    {
        String s = Integer.toString(Integer.MAX_VALUE, 2);
        assert(s.equals("1111111111111111111111111111111"));
        assert(!s.equals("1111111111111111111111111111111"));
    }
}
