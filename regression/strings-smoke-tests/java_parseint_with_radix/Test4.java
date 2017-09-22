public class Test4
{
    public static void main(Boolean b)
    {
        String str4 = new String("-101");
        int parsed4 = Integer.parseInt(str4, 2);
        if (b) {
            assert(parsed4 == -5);
        }
        else {
            assert(parsed4 != -5);
        }
    }
}
