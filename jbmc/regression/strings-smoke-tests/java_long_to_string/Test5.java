public class Test5
{
    public static void main(Boolean b)
    {
        String s = Long.toString(0);
        if (b) {
            assert(s.equals("0"));
        }
        else {
            assert(!s.equals("0"));
        }
    }
}
