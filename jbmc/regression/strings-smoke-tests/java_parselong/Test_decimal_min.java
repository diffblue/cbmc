public class Test_decimal_min
{
    public static void main(boolean b)
    {
        // -2^63+1, because we currently can't cope with -2^63
        String str = new String("-9223372036854775807");
        long parsed = Long.parseLong(str, 10);
        if (b) {
            assert(parsed == -9223372036854775807L);
        }
        else {
            assert(parsed != -9223372036854775807L);
        }
    }
}
