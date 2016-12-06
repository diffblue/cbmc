public class test_int {

    public static void main(String[] argv) {
	String s = Integer.toString(2345);
	char c = s.charAt(1);
	char d = s.charAt(2);
	char e = s.charAt(3);
	assert(c == '3');
	assert(d == '4');

	int i = Integer.parseInt("1234");
	assert(i == 1234);

	String t = Integer.toString(-2345);
	assert(t.charAt(0) == '-');
	
	int j = Integer.parseInt("-4231");
	assert(j == -4231);

	String u = Integer.toHexString(43981);
	assert(u.equals("abcd"));

	assert(e == '2' || i < 1234 || t.charAt(0) != '-' || j != -4231 || !u.equals("abcd"));
    }
}
