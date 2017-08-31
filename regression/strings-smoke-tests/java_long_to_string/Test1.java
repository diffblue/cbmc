public class Test1
{
    public static void main(Boolean b)
    {
        String s = Long.toString(12);
        if (b) {
            assert(s.equals("12"));
        }
        else {
            assert(!s.equals("12"));
        }
    }
}
