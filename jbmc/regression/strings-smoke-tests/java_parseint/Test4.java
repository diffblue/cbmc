public class Test4
{
    public static void main(String input_string)
    {
        if(input_string.length() == 2) {
            assert(Integer.parseInt(input_string) != 50);
        }
        else if(input_string.length() == 4) {
            assert(!input_string.equals("XYZW"));
        }
    }
}
