public class test_delete {

    public static void main(String[] argv) {
	StringBuilder s = new StringBuilder();
	s.append("Hello World!");
	s.delete(4,6);
	s.deleteCharAt(1);

	String str = s.toString();
	System.out.println(str);
	assert(str.equals("HllWorld!"));
	assert(!str.equals("HllWorld!"));

    }
}
