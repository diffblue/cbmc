public class Test_hex3
{
    public static void main(Boolean b)
    {
        String s = Integer.toString(Integer.MIN_VALUE + 1, 16);
        if (b) {
            assert(s.equals("-7fffffff"));
        }
        else {
            assert(!s.equals("-7fffffff"));
        }
    }
}
