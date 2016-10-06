public class test_char_at {

    public static void main(String[] argv) {
	String s = new String("Hello World!");
	char c = s.charAt(4);
	StringBuilder sb = new StringBuilder(s);
	sb.setCharAt(5,'-');
	s = sb.toString();

	if(argv.length==1)
	    assert(c == 'o');
	else if(argv.length==2)
	    assert(c == 'p');
	else
	    assert(s.equals("Hello-World!"));
    }
}
