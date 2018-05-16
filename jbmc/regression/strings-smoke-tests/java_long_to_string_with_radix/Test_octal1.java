public class Test_octal1
{
    public static void main(Boolean b)
    {
        String s = Long.toString(-23, 8);
        if (b) {
            assert(s.equals("-27"));
        }
        else {
            assert(!s.equals("-27"));
        }
    }
}
