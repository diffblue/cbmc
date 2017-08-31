public class Test_hex3
{
    public static void main(Boolean b)
    {
        String s = Long.toString(Long.MIN_VALUE + 1, 16);
        if (b) {
            assert(s.equals("-7fffffffffffffff"));
        }
        else {
            assert(!s.equals("-7fffffffffffffff"));
        }
    }
}
