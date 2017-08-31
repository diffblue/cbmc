public class Test_binary
{
    public static void main(Boolean b)
    {
        String s = Integer.toString(Integer.MIN_VALUE, 2);
        if (b) {
            assert(s.equals("-10000000000000000000000000000000"));
        }
        else {
            assert(!s.equals("-10000000000000000000000000000000"));
        }
    }
}
