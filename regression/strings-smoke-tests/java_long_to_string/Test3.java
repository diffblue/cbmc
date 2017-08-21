public class Test3
{
    public static void main(Boolean b)
    {
        String s = Long.toString(Long.MAX_VALUE);
        if (b) {
            assert(s.equals("9223372036854775807"));
        }
        else {
            assert(!s.equals("9223372036854775807"));
        }
    }
}
