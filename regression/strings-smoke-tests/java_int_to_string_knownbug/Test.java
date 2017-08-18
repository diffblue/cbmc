public class Test
{
    public static void main(Boolean b)
    {
        String t = Integer.toString(Integer.MIN_VALUE);
        if (b) {
            assert(t.equals("-2147483648"));
        }
        else {
            assert(!t.equals("-2147483648"));
        }
    }
}
