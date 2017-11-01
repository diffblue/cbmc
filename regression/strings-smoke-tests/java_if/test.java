public class test
{
    public static String main(int i)
    {
        Object t[] = new Object[5];
        t[0] = "world!";
        StringBuilder s = new StringBuilder("Hello ");
        if(t[0] instanceof String)
            s.append((String) t[0]);
        if(i == 0)
            assert(s.toString().equals("Hello world!"));
        else
            assert(!s.toString().equals("Hello world!"));
        return s.toString();
    }
}
