public class test_char_array {

    public static void test_init() 
    {
	char [] str = new char[10];
	str[0] = 'H';
	str[1] = 'e';
	str[2] = 'l';
	str[3] = 'l';
	str[4] = 'o';
	String s = new String(str);
	char c = str[2];
	assert(s.equals("Hello"));
	assert(!s.equals("Hello"));
    }

    /*
    public static void test_to_array(String t)
    {
	String s = "abc";
	char [] str = s.toCharArray();
	char c = str[2];
	char d = t.charAt(0);


	assert(str.length == 3);
	assert(c == 'c');
	assert(c == d || d < 'a' || d > 'z' );
    }
    */
    public static void main(String[] argv) 
    {
	test_init();
	// test_to_array(argv[0]);
    }
}
