public class Test
{
    public static void foo()
    {
        // -2^35
        String str = new String("-100000000000000000000000000000000000");
        long parsed = Long.parseLong(str, 2);
        assert(parsed == -34359738368L);
        assert(parsed != -34359738368L);
    }
}
