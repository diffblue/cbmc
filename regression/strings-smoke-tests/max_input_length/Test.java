public class Test {
    public static void main(String s) {
	// This prevent anything from happening if string-max-length is smaller
	// than 40
	String t = new String("0123456789012345678901234567890123456789");
	if (s.length() >= 30)
	    // This should not happen when string-max-input length is smaller
	    // than 30
	    assert false;
    }
}
