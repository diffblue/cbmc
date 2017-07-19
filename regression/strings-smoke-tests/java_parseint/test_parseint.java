public class test_parseint
{
    public static void main(String[] args)
    {
        if (args.length == 1) {
            String twelve = new String("12");
            int parsed1 = Integer.parseInt(twelve);
            assert(parsed1 == 12);
            assert(parsed1 != 12);
        }
    }
}
