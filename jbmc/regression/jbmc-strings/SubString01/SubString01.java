public class SubString01
{
    public static void main(String[] args)
    {
        String letters = "automatictestcasegenerationatdiffblue";

        String tmp=org.cprover.CProverString.substring(letters, 20);
        assert tmp.equals("erationatdiffblue");
        tmp=org.cprover.CProverString.substring(letters, 9, 13);
        assert tmp.equals("test");
    }
}
