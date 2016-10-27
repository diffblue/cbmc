public class test_insert {

    public static void main(String[] argv) {
	int i = 123;
	long j = 123;
	char c = '/';
	boolean b = true;
	StringBuilder sb = new StringBuilder("hello");
	sb.insert(2,i);
	sb.insert(2,c);
	sb.insert(2,j);
	sb.insert(2,b);
	sb.insert(2,"abc");
	String s = sb.toString();
	System.out.println(s);
	assert(s.equals("heabctrue123/123llo"));
	assert(!s.equals("heabctrue123/123llo"));
    }
}
