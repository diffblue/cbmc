public class Test_hex1
{
    public static void main(Boolean b)
    {
        String s = Integer.toString(-27, 16);
        if (b) {
            assert(s.equals("-1b"));
        }
        else {
            assert(!s.equals("-1b"));
        }
    }
}
