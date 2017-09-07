public class Test5
{
    public static void main(Boolean b)
    {
        String str5 = new String("00aB");
        int parsed5 = Integer.parseInt(str5, 16);
        if (b) {
            assert(parsed5 == 171);
        }
        else {
            assert(parsed5 != 171);
        }
    }
}
