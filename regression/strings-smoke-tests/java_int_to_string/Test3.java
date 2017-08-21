public class Test3
{
    public static void main(Boolean b)
    {
        String s = Integer.toString(Integer.MAX_VALUE);
        if (b) {
            assert(s.equals("2147483647"));
        }
        else {
            assert(!s.equals("2147483647"));
        }
    }
}
