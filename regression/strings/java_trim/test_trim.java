public class test_trim {
    public static void main(String[] argv) {
	String t = "  a b c  ";
	String x = t.trim();
	assert(x.equals("a b c"));
	assert(x.equals("abc "));
    }
}
