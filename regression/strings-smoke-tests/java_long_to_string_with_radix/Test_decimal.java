public class Test_decimal
{
    public static void main(Boolean b)
    {
        String s = Long.toString(-27, 10);
        if (b) {
            assert(s.equals("-27"));
        }
        else {
            assert(!s.equals("-27"));
        }
    }
}
