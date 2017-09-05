public class test_append_char
{
    public static String ofCharArray(char arr[])
    {
        StringBuilder sb = new StringBuilder("");
        for(int i = 0; i < arr.length; i++)
            sb.append(arr[i]);
        return sb.toString();
    }
    public static void main(String[] args)
    {
        char[] diff = {'d', 'i', 'f', 'f'};
        char[] blue = {'b', 'l', 'u', 'e'};

        StringBuilder buffer = new StringBuilder();

        buffer.append(ofCharArray(diff))
              .append(ofCharArray(blue));

        String tmp=buffer.toString();
        System.out.println(tmp);
        if(args.length == 0)
            assert tmp.equals("diffblue");
        else
            assert !tmp.equals("diffblue");
    }
}
