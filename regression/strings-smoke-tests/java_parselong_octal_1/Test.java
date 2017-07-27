public class Test
{
    public static void foo()
    {
        String str = new String("7654321076543210");
        long parsed = Long.parseLong(str, 8);
        assert(parsed == 275730608604808L);
        assert(parsed != 275730608604808L);
    }
}
