public class Test1
{
    public static void main(Boolean b)
    {
        String str1 = new String("F");
        int parsed1 = Integer.parseInt(str1, 16);
        if (b) {
            assert(parsed1 == 15);
        }
        else {
            assert(parsed1 != 15);
        }
    }
}
