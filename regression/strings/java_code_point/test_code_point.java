public class test_code_point {

    public static void main(String[] argv) {
	String s = "!𐤇𐤄𐤋𐤋𐤅"; 
	assert(s.codePointAt(1) == 67847);
	assert(s.codePointBefore(3) == 67847);
	assert(s.codePointCount(1,5) >= 2);
    }
}
