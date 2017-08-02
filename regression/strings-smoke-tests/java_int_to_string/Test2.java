public class Test2
{
    public static void main()
    {
        String s = Integer.toString(-23);
        assert(s.equals("-23"));
        assert(!s.equals("-23"));
    }
}
