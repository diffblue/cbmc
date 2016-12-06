public class test_case {

    public static void main(String[] argv) {

	String s = new String("AbcCdE");
	String l = s.toLowerCase();
	System.out.println(l);
	
	String u = s.toUpperCase();
	System.out.println(u);
	assert(l.equals("abccde"));
	assert(u.equals("ABCCDE"));
	assert(s.equalsIgnoreCase("ABccDe"));
	assert(!l.equals("abccde") || !u.equals("ABCCDE"));
    }
}
