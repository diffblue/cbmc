public class test_insert_char_array
{
    // These are models of the String methods manipulating char arrays
    public static String stringOfCharArray(char arr[])
    {
        StringBuilder sb=new StringBuilder("");
        for(int i=0; i<arr.length; i++)
            sb.append(arr[i]);
        return sb.toString();
    }
    public static void insert(StringBuilder sb, int pos, char arr[])
    {
        String s=stringOfCharArray(arr);
        sb.insert(pos, s);
    }
    public static void main(int i)
    {
        StringBuilder sb = new StringBuilder("ad");
        char[] array = new char[2];
        array[0] = 'b';
        array[1] = 'c';
        insert(sb, 1, array);
        String s = sb.toString();
        System.out.println(s);
        if(i==0)
            assert(s.equals("abcd"));
        else
            assert(!s.equals("abcd"));
    }
}
