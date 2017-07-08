public class StringValueOfBool
{
    public static void main()
    {
        boolean booleanValue = false;

        String tmp=String.valueOf(booleanValue);
        assert tmp.equals("false");
    }
}
