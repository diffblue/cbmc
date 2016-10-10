public class test_compare {

    public static void main(String[] argv) {
	String s1 = "abc";
	String s2 = "aac";
	assert(s1.compareTo(s2) == 1);

	assert(s2.compareTo(argv[0]) != -1);
    }
}
