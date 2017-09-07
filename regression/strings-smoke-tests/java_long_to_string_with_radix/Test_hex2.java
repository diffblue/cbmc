public class Test_hex2
{
    public static void main(Boolean b)
    {
        String s = Long.toString(Long.MAX_VALUE, 16);
        if (b) {
            assert(s.equals("7fffffffffffffff"));
        }
        else {
            assert(!s.equals("7fffffffffffffff"));
        }
    }
}
