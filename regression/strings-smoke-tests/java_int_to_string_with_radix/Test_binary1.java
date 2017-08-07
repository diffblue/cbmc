public class Test_binary1
{
    public static void main()
    {
        String s = Integer.toString(-23, 2);
        assert(s.equals("-10111"));
        assert(!s.equals("-10111"));
    }
}
