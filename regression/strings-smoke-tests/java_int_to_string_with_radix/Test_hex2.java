public class Test_hex2
{
    public static void main(Boolean b)
    {
        String s = Integer.toString(Integer.MAX_VALUE, 16);
        if (b) {
            assert(s.equals("7fffffff"));
        }
        else {
            assert(!s.equals("7fffffff"));
        }
    }
}
