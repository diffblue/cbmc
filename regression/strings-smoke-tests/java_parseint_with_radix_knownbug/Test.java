public class Test
{
    public static void foo(int i)
    {
        if (i == 1) {
            // 2^31-1, max value of Integer
            String str1 = new String("7FFFFFFF");
            int parsed1 = Integer.parseInt(str1, 16);
            assert(parsed1 == 2147483647);
            assert(parsed1 != 2147483647);
        }
        else if (i == 2) {
            // -2^31, min value of Integer, and longest string we could have
            String str2 = new String("-100000000000000000000000000000000");
            int parsed2 = Integer.parseInt(str2, 2);
            assert(parsed2 == -2147483648);
            assert(parsed2 != -2147483648);
        }
   }
}
