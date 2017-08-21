public class Test_octal
{
    public static void main(Boolean b)
    {
        String s = Integer.toString(Integer.MIN_VALUE, 8);
        if (b) {
            assert(s.equals("-20000000000"));
        }
        else {
            assert(!s.equals("-20000000000"));
        }
    }
}
