public class test_empty {
    public static void main(String[] argv) {
	String empty = "   ";
	assert(empty.trim().isEmpty());
	assert(empty.isEmpty());
    }
}
