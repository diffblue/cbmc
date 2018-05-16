public class Test_decimal_max
{
    public static void main(boolean b)
    {
        // 2^63+1
        String str = new String("9223372036854775807");
        long parsed = Long.parseLong(str);
        if (b) {
            assert(parsed == 9223372036854775807L);
        }
        else {
            assert(parsed != 9223372036854775807L);
        }
    }
}
