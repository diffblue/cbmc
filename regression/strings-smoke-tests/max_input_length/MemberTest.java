public class MemberTest {
    String foo;
    public void main() {
        // Causes this function to be ignored if string-max-length is
        // less than 40
        String t = new String("0123456789012345678901234567890123456789");
        assert foo != null && foo.length() < 30;
    }
}
