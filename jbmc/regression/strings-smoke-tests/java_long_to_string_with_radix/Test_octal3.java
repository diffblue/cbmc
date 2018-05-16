public class Test_octal3
{
    public static void main(Boolean b)
    {
        String s = Long.toString(Long.MIN_VALUE + 1, 8);
        if (b) {
            assert(s.equals("-777777777777777777777"));
        }
        else {
            assert(!s.equals("-777777777777777777777"));
        }
    }
}
