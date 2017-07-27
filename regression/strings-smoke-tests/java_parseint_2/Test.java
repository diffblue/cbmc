public class Test
{
    public static void foo(String input_string)
    {
        int parsed1 = Integer.parseInt(input_string);
        if (parsed1 == 2) {
            assert(false);
        }
    }
}
