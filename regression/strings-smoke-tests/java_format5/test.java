public class test
{
    public static String main(boolean b)
    {
        String s = String.format("%s%s%s%s%s%s%s%s", "a", "b", "c", "d", "e", "f", "g", "h");
        if(b)
            assert(s.equals("abcdefgh"));
        else
            assert(!s.equals("abcdefgh"));
        return s;
    }
}
