public class MemberTest {
    String foo;

    public void main() {
        if (foo == null)
          return;

        // This would prevent anything from happening if we were to add a
        // constraints on strings being smaller than 40
        String t = new String("0123456789012345678901234567890123456789");

        if (foo.length() >= 30)
            // This should not happen when string-max-input length is smaller
            // than 30
            assert false;
    }
}
