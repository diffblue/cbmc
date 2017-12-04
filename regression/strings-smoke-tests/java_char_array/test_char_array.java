public class test_char_array
{
    // This is a model of the String.toCharArray method
    public static char[] toCharArray(String s)
    {
        int length = s.length();
        assert(length < 5);
        char arr[] = new char[s.length()];
        // We limit arbitrarly the loop unfolding to 5
        for(int i = 0; i < length && i < 5; i++)
            arr[i] = org.cprover.CProverString.charAt(s, i);
        return arr;
    }

    public static void main(int i)
    {
        String s = "abc";
        char [] str = toCharArray(s);
        char c = str[2];
        char a = org.cprover.CProverString.charAt(s, 0);
        assert(str.length == 3);
        assert(a == 'a');
        assert(c == 'c');
        if(i == 0)
            assert(str.length != 3);
        if(i == 2)
            assert(a != 'a');
        if(i == 3)
            assert(c != 'c');
    }
}
