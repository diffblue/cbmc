public class test_parselong
{
    public static void main(String[] args)
    {
        // -(2^63 - 1) - note that -2^63 should work but doesn't because of a
        // limitation in the current code
        String str = new String("-111111111111111111111111111111111111111111111111111111111111111");
        long parsed = Long.parseLong(str, 2);
        assert(parsed == -9223372036854775807L);
        assert(parsed != -9223372036854775807L);
    }
}
