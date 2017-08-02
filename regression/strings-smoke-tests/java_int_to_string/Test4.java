public class Test4
{
    public static void main()
    {
        String s = Integer.toString(Integer.MIN_VALUE + 1);
        assert(s.equals("-2147483647"));
        assert(!s.equals("-2147483647"));
    }
}
