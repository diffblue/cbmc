public class Test5
{
    public static void main()
    {
        String s = Integer.toString(0);
        assert(s.equals("0"));
        assert(!s.equals("0"));
    }
}
