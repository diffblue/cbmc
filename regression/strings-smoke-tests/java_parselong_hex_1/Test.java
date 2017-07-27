public class Test
{
    public static void foo()
    {
        String str = new String("+00AbCdEf0123");
        long parsed = Long.parseLong(str, 16);
        assert(parsed == 737894400291L);
        assert(parsed != 737894400291L);
    }
}
