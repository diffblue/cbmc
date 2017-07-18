public class test_parseint_with_radix
{
    public static void main(String[] args)
    {
        // -2^31, min value of Integer, and longest string we could have
        String str2 = new String("-100000000000000000000000000000000");
        int parsed2 = Integer.parseInt(str2, 2);
        assert(parsed2 == -2147483648);
        assert(parsed2 != -2147483648);
    }
}
