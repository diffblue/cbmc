public class test_suffix {

    public static void main(String[] argv) {
	String s = new String("Hello World!");
	//String t = new String("Hello");
	//String u = new String("Wello");
	String u = "Wello!";
	boolean b = s.endsWith("World!");
	//boolean c = s.startsWith("Wello");
	//boolean b = s.startsWith(t);
	boolean c = s.startsWith(u);
	assert(b);	
	assert(c);
    }
}
