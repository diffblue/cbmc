public class test_init
{
    // These are models for the constructors of strings from char arrays
    public static String stringOfCharArray(char arr[])
    {
        // We give an arbitrary limit on the size of arrays
        assert(arr.length<11);
        StringBuilder sb=new StringBuilder("");
        for(int i=0; i<arr.length && i<11; i++)
            sb.append(arr[i]);
        return sb.toString();
    }

    public static String stringOfCharArray(char arr[], int i, int j)
    {
        return org.cprover.CProverString.substring(stringOfCharArray(arr), i, i+j);
    }

    public static void main(int i)
    {
        char [] str = new char[10];
        str[0] = 'H';
        str[1] = 'e';
        str[2] = 'l';
        str[3] = 'l';
        str[4] = 'o';
        String s = stringOfCharArray(str);
        String t = stringOfCharArray(str,1,2);

        if(i==0)
            assert(s.startsWith("Hello"));
        else if(i==1)
            assert(t.equals("el"));
        else if(i==2)
            assert(!s.startsWith("Hello"));
        else
            assert(!t.equals("el"));
    }
}
