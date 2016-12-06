public class test_length {

    public static void main(String[] argv) {
	String s = new String("hello");
	if(argv.length > 1) {
	    String t = argv[1];
	    int i = t.length();
	    String u = t.concat(s);
	    char c = u.charAt(i);
	    assert(c == 'h');
	    assert(c == 'o');
	}
    }
}
