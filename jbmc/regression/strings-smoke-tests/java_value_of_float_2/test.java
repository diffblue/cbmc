public class test
{
    public static void check()
    {
        String s3=String.valueOf(7.89e12f);
        assert(s3.equals("7.89E12"));
        assert(!s3.equals("7.89E12"));
    }
}
