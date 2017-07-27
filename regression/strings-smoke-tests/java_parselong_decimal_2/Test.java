public class Test
{
    public static void foo()
    {
        // -2^41
        String str = new String("-2199023255552");
        long parsed = Long.parseLong(str, 10);
        assert(parsed == -2199023255552L);
        assert(parsed != -2199023255552L);
    }
}
