public class Test_octal2
{
    public static void main(Boolean b)
    {
        String s = Long.toString(Long.MAX_VALUE, 8);
        if (b) {
            assert(s.equals("777777777777777777777"));
        }
        else {
            assert(!s.equals("777777777777777777777"));
        }
    }
}
