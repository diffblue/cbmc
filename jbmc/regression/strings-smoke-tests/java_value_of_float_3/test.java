public class test
{
    public static void check()
    {
        String s5=String.valueOf(5.67e-9f);
        // The result may not be exactly 5.67E-9 as 5.66999...E-9 is also valid
        assert(s5.startsWith("5.6") && s5.endsWith("E-9"));
        assert(!s5.startsWith("5.6") || !s5.endsWith("E-9"));
    }
 }
