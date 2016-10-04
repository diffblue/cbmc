public class test_delete {

    public static void main(String[] argv) {
	StringBuilder s = new StringBuilder();
	s.append("Hello "); //o World!");
	//s.delete(4,6);
	s.delete(1,2);
	//s.deleteCharAt(4);
	String str = s.toString();
	System.out.println(str);
	assert(str.startsWith("Hllo"));
	//assert(!str.equals("Hllo World"));
	//assert(str.equals("HllWorld!"));
	//assert(!str.equals("HllWorld!"));

    }
}
