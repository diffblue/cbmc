public class test
{
    public static String main()
    {
        String s = String.format("foo %s", "bar");
        assert(s.equals("foo bar"));
        assert(!s.equals("foo bar"));
        return s;
    }
}
