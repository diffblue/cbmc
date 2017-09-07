public class Test2
{
    public static void main(Boolean b)
    {
        String str2 = new String("123");
        int parsed2 = Integer.parseInt(str2, 10);
        if (b) {
            assert(parsed2 == 123);
        }
        else {
            assert(parsed2 != 123);
        }
    }
}
