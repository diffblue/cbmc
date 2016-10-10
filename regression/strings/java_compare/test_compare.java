public class test_compare {

    public static void main(String[] argv) {
	String s1 = "abc";
	String s2 = "aac";
	assert(s1.compareTo(s2) == 1);

	assert(s2.compareTo(argv[0]) != -1);
	
	String s3 = "abc";
	assert(s3.hashCode() == s1.hashCode());
	assert(s3.hashCode() == s2.hashCode());
			  
	/*String x = s1.intern();
	String y = s3.intern();
	assert(x == y);*/
    }
}
