public class Test2
{
    public static void main(Boolean b)
    {
        // 2^31-1, max value of Integer
        String max_int = new String("2147483647");
        int parsed2 = Integer.parseInt(max_int);
        if (b) {
            assert(parsed2 == 2147483647);
        }
        else{
            assert(parsed2 != 2147483647);
        }
    }
}
