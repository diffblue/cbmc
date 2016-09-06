public class test_char_at {

    public static void main(String[] argv) {
	String s = new String("Hello World!");
	char c = s.charAt(4);
	assert(c == 'o');
	assert(c == 'p');
    }
}
