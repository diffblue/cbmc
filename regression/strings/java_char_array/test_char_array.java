public class test_char_array {

    public static void main(String[] argv) {
	String s = "abc";
	//char[] str = new char[12];
	char [] str = s.toCharArray();
	char c = str[2];
	String t = argv[0];
	//str[3]='0';
	//assert(str.length == 3);
	char d = t.charAt(0);
	assert(c == 'c');
	assert(c == d || d < 'a' || d > 'z' );
    }
}
