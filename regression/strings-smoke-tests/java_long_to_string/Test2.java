public class Test2
{
    public static void main(Boolean b)
    {
        String s = Long.toString(-23);
        if (b) {
            assert(s.equals("-23"));
        }
        else {
            assert(!s.equals("-23"));
        }
    }
}
