public class Test_octal2
{
    public static void main(Boolean b)
    {
        String s = Integer.toString(Integer.MAX_VALUE, 8);
        if (b) {
            assert(s.equals("17777777777"));
        }
        else {
            assert(!s.equals("17777777777"));
        }
    }
}
