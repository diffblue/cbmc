public class Test3
{
    public static void main(Boolean b)
    {
        String str3 = new String("77");
        int parsed3 = Integer.parseInt(str3, 8);
        if (b) {
            assert(parsed3 == 63);
        }
        else {
            assert(parsed3 != 63);
        }
    }
}
