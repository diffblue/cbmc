public class test
{
    public static void check()
    {
        String s7=String.valueOf(java.lang.Float.POSITIVE_INFINITY);
        String s8=String.valueOf(java.lang.Float.NEGATIVE_INFINITY);
        String s9=String.valueOf(java.lang.Float.NaN);
        assert(s7.equals("Infinity"));
        assert(s8.equals("-Infinity"));
        assert(s9.equals("NaN"));
        assert(!s7.equals("Infinity") || !s8.equals("-Infinity") || !s9.equals("NaN"));
    }
}
