public class test_parselong
{
    public static void main(String[] args)
    {
        // 2^40
        String str = new String("1099511627776");
        long parsed = Long.parseLong(str);
        assert(parsed == 1099511627776L);
        assert(parsed != 1099511627776L);
    }
}
