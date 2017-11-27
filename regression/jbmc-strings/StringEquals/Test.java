public class Test {
    public static void check(int i, String s) {
        String t = "Hello World";
        Integer x = new Integer(2);
        if (i==0)
            assert("Hello World".equals(t));
        else if (i==1)
            assert(! "Hello World".equals(s));
        else if (i==2)
            assert(! "Hello World".equals(x));
        else if (i==3)
            assert("Hello World".equals(x));
        else if (i==4)
            assert(! s.equals(x));
        else if (i==5)
            assert(s.equals(x));
    }
}
