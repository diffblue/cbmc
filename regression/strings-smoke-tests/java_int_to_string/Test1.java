public class Test1
{
    public static void main()
    {
        String s = Integer.toString(12);
        assert(s.equals("12"));
        assert(!s.equals("12"));
    }
}
