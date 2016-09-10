public class test_prefix {

    public static void main(String[] argv) {
	String s = new String("Hello World!");
	//String t = new String("Hello");
	//String u = new String("Wello");
	String t = "Hello";
	String u = new String("Wello");
	//boolean b = s.startsWith("Hello");
	//boolean c = s.startsWith("Wello");
	boolean b = s.startsWith(t);
	boolean c = s.startsWith(u);
	assert(b);	
	assert(c);
    }
}
