public class test_substring {

    public static void main(String[] argv) {
	if(argv.length > 1) {
	    String t = argv[1];

	    if(t.length() == 6) {
		String u = t.substring(2,4);
		char c = u.charAt(1);
		char d = t.charAt(3);
		char e = t.charAt(4);
		assert(c == d);
		assert(c == e);
	    }
	    else if(t.length() == 5){
		CharSequence u = t.subSequence(2,4);
		char c = u.charAt(1);
		char d = t.charAt(3);
		char e = t.charAt(4);
		assert(c == d);
		assert(c == e);
	    }
		

	}
    }
}
