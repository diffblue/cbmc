public class Test_octal3
{
    public static void main(Boolean b)
    {
        String s = Integer.toString(Integer.MIN_VALUE + 1, 8);
        if (b) {
            assert(s.equals("-17777777777"));
        }
        else {
            assert(!s.equals("-17777777777"));
        }
    }
}
