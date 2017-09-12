public class test
{
    public static String main()
    {
        Object t[] = new Object[5];
        t[0] = "world!";
        StringBuilder s = new StringBuilder("Hello ");
        if(t[0] instanceof String)
        {
            s.append((String) t[0]);
        }
        assert(s.toString().equals("Hello world!"));
        assert(!s.toString().equals("Hello world!"));
        return s.toString();
    }
}
