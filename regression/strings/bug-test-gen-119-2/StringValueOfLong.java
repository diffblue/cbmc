public class StringValueOfLong
{
    public static void main()
    {
        long longValue = 10000000000L; // L suffix indicates long
        String tmp=String.valueOf(longValue);
        assert tmp.equals("10000000000");
    }
}
