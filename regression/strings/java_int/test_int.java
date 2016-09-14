public class test_int {

    public static void main(String[] argv) {
	//StringBuilder s = new StringBuilder();
	String s = Integer.toString(2345);
	char c = s.charAt(1);
	char d = s.charAt(2);
	char e = s.charAt(3);
	assert(c == '3');
	assert(d == '4');
	assert(e == '2');
    }
}
