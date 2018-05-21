public class test
{
    public static void check(int i)
    {
        String s = String.valueOf(123.456f);
        if(i == 1)
            assert(s.equals("123.456"));
        else
            assert(!s.equals("123.456"));
    }
}