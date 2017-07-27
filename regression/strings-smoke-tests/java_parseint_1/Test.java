public class Test
{
    public static void foo(int i)
    {
        if (i == 1) {
            String twelve = new String("12");
            int parsed1 = Integer.parseInt(twelve);
            assert(parsed1 == 12);
            assert(parsed1 != 12);
        }
        else if (i == 2) {
            // 2^31-1, max value of Integer
            String max_int = new String("2147483647");
            int parsed2 = Integer.parseInt(max_int);
            assert(parsed2 == 2147483647);
            assert(parsed2 != 2147483647);
        }
    }
}
