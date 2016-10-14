public class test_contains {

    public static void main(String[] argv) {
	String s = new String("Hello World!");
	String u = "o W";
	String t = "W o";
	assert(s.contains(u));	
	assert(s.contains(t));
    }
}
