public class Test4
{
    public static void main(Boolean b)
    {
        String s = Long.toString(Long.MIN_VALUE + 1);
        if (b) {
            assert(s.equals("-9223372036854775807"));
        }
        else {
            assert(!s.equals("-9223372036854775807"));
        }
    }
}
