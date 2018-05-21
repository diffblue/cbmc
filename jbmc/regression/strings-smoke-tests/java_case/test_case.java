public class test_case
{
    public static void main(int i)
    {
        String s = new String("Ab");
        String l = s.toLowerCase();
        String u = s.toUpperCase();
        if(i==1)
        {
            assert(l.equals("ab"));
            assert(u.equals("AB"));
            assert(s.equalsIgnoreCase("aB"));
        }
        else if(i==2)
        {
            assert(!u.equals("AB"));
        }
        else if(i==3)
        {
            assert("ÖÇ".toLowerCase().equals("öç"));
        }
        else
        {
            assert(!"ÖÇ".toLowerCase().equals("öç"));
        }
    }
}
