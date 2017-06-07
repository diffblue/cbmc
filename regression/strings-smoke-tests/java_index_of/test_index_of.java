public class test_index_of
{
    public static void main(/*String[] argv*/)
    {
        String s = "Abc";
        String bc = "bc";
        String ab = "ab";
        int i = s.indexOf(bc);
        int j = s.indexOf(ab);
        assert(i == 1);
        assert(j == -1);
    }
}
