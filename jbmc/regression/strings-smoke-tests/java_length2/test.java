public class test
{
    public static int check(String s)
    {
        if(s.equals("abc")){
            assert s.length() == 3;
            return 0;
        }
        return 1;
    }
}

