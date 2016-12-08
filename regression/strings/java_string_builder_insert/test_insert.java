public class test_insert {

    public static void main(String[] argv)
    {
	char [] str = new char[5];
	str[0] = 'H';
	str[1] = 'e';
	str[2] = 'l';
	str[3] = 'l';
	str[4] = 'o';


	StringBuilder sb = new StringBuilder(" world");
	sb.insert(0,str);
	String s = sb.toString();
	System.out.println(s);
	assert(s.equals("Hello world"));
	assert(!s.equals("Hello world"));
    }
}
