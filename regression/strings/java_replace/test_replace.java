public class test_replace {

    public static void main(String[] argv) {
	String s = new String("Hello World!");
	String t = s.replace('o','u');
	assert(t.equals("Hellu Wurld!"));
	System.out.println(t);
	assert(!t.equals("Hellu Wurld!"));
    }
}
