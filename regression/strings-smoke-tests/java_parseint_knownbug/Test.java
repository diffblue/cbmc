public class Test
{
    public static void foo()
    {
        // -2^31, min value of Integer, and longest string we could have without
        // leading zeroes
        String min_int = new String("-2147483648");
        int parsed3 = Integer.parseInt(min_int);
        assert(parsed3 == -2147483648);
        assert(parsed3 != -2147483648);
    }
}
