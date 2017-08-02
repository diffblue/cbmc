public class Test3
{
    public static void main()
    {
        String s = Integer.toString(Integer.MAX_VALUE);
        assert(s.equals("2147483647"));
        assert(!s.equals("2147483647"));
    }
}
