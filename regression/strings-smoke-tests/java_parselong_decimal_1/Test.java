public class Test
{
    public static void foo()
    {
        // 2^40
        String str = new String("1099511627776");
        long parsed = Long.parseLong(str);
        assert(parsed == 1099511627776L);
        assert(parsed != 1099511627776L);
    }
}
