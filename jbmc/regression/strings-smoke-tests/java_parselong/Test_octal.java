public class Test_octal
{
    public static void main(boolean b)
    {
        String str = new String("7654321076543210");
        long parsed = Long.parseLong(str, 8);
        if (b) {
            assert(parsed == 275730608604808L);
        }
        else {
            assert(parsed != 275730608604808L);
        }
    }
}
