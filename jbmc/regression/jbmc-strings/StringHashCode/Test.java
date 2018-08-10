public class Test {

    public static int check(String s, int nondet) {
        if(s == null)
            return -1;

        if(nondet == 0) {
            // This is always true
            assert "foo".hashCode() == 101574;
        } else if(nondet == 1) {
            // This is always false
            assert "foo".hashCode() != 101574;
        } else if(nondet == 2) {
            // This is sometimes false
            assert !s.startsWith("foo") && s.hashCode() == 101574;
        } else if(nondet == 3) {
            // This is always true
            assert s.hashCode() == 101574 || !(s.startsWith("foo") && s.length() == 3);
        } else {
            // This is always false
            assert "bar".hashCode() == 101574;
        }

        return s.hashCode();
    }
}
