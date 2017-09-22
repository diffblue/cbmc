public class test
{
    public static String main(String str)
    {
        try
        {
            String s = String.format("%s %s", "a");
            assert(false);
            return s;
        }
        catch(java.util.IllegalFormatException e)
        {
            assert(false);
            return str;
        }
    }
}
