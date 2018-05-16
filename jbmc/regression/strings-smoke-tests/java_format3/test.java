public class test
{
    public static String main(int i)
    {
        String s = String.format("%3$sar", "a", "r", "b");
        if(i==0)
            assert(s.equals("bar"));
        else
            assert(!s.equals("bar"));
        return s;
    }
}
