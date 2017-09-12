public class test
{

    public static void main(String[] args)
    {
        char c = 'a';
        if(args.length>1)
            assert Character.getNumericValue(c) == 10;
        else
            assert Character.getNumericValue(c) != 10;
    }
}
