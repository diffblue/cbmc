public class Test
{
    public static void main(Boolean b)
    {
        // -2^31, min value of Integer, and longest string we could have
        String str = new String("-100000000000000000000000000000000");
        int parsed = Integer.parseInt(str, 2);
        if (b) {
            assert(parsed == -2147483648);
        }
        else {
            assert(parsed != -2147483648);
        }
   }
}
