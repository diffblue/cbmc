public class Test4
{
    public static void main(Boolean b)
    {
        String s = Integer.toString(Integer.MIN_VALUE + 1);
        if (b) {
            assert(s.equals("-2147483647"));
        }
        else {
            assert(!s.equals("-2147483647"));
        }
    }
}
