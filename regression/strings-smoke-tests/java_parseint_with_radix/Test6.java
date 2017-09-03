public class Test6
{
    public static void main(Boolean b)
    {
        // 2^31-1, max value of Integer
        String str1 = new String("7FFFFFFF");
        int parsed1 = Integer.parseInt(str1, 16);
        if (b) {
            assert(parsed1 == 2147483647);
        }
        else{
            assert(parsed1 != 2147483647);
        }
    }
}
