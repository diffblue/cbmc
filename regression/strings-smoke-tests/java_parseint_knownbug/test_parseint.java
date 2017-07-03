public class test_parseint
{
    public static void main(String[] args)
    {
        if (args.length == 2) {
            // 2^31-1, max value of Integer
            String max_int = new String("2147483647");
            int parsed2 = Integer.parseInt(max_int);
            assert(parsed2 == 2147483647);
            assert(parsed2 != 2147483647);
        }
        else if (args.length == 3) {
            // -2^31, min value of Integer, and longest string we could have without
            // leading zeroes
            String min_int = new String("-2147483648");
            int parsed3 = Integer.parseInt(min_int);
            assert(parsed3 == -2147483648);
            assert(parsed3 != -2147483648);
        }
    }
}
