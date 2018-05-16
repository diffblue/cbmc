public class test
{
    public static String main(String str)
    {
        String s = String.format("foo %s", str);
        assert(s.equals("foo ".concat(str)));
        assert(!s.equals("foo ".concat(str)));
        return s;
    }
}
