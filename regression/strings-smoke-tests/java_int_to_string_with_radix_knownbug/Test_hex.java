public class Test_hex
{
    public static void main(Boolean b)
    {
        String s = Integer.toString(Integer.MIN_VALUE, 16);
        if (b) {
            assert(s.equals("-80000000"));
        }
        else {
            assert(!s.equals("-80000000"));
        }
    }
}
