public class Test1
{
    public static void main(Boolean b)
    {
        String twelve = new String("12");
        int parsed1 = Integer.parseInt(twelve);
        if (b) {
            assert(parsed1 == 12);
        }
        else {
            assert(parsed1 != 12);
        }
    }
}
