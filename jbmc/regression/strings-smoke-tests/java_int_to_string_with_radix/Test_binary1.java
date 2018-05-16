public class Test_binary1
{
    public static void main(Boolean b)
    {
        String s = Integer.toString(-23, 2);
        if (b) {
            assert(s.equals("-10111"));
        }
        else {
            assert(!s.equals("-10111"));
        }
    }
}
