public class Test
{
    public static void main(Boolean b)
    {
        // -2^31, min value of Integer, and longest string we could have without
        // leading zeroes
        String min_int = new String("-2147483648");
        int parsed3 = Integer.parseInt(min_int);
        if (b) {
            assert(parsed3 == -2147483648);
        }
        else {
            assert(parsed3 != -2147483648);
        }
    }
}
