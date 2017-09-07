public class Test_binary3
{
    public static void main(Boolean b)
    {
        String s = Long.toString(Long.MIN_VALUE + 1, 2);
        if (b) {
            assert(s.equals("-111111111111111111111111111111111111111111111111111111111111111"));
        }
        else {
            assert(!s.equals("-111111111111111111111111111111111111111111111111111111111111111"));
        }
    }
}
