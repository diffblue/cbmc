public class Test_other_branches_possible
{
    public static void main(String input_string)
    {
        if(input_string.length() == 2) {
            assert(Long.parseLong(input_string) != 50);
        }
        else if(input_string.length() == 4) {
            assert(!input_string.equals("XYZW"));
        }
    }
}
