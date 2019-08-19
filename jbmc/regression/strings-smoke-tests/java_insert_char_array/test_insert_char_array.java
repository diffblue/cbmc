public class test_insert_char_array
{
    public static void insert(StringBuilder sb, int offset, char[] arr)
    {
        assert(arr.length<5);
        for(int i=0; i<arr.length && i<5; i++)
          sb.insert(offset + i, arr[i]);
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
