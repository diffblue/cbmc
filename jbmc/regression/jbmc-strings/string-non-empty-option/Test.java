public class Test {

    static void checkMinLength(String arg1, String arg2, int nondet) {
        // Filter
        if (arg1 == null || arg2 == null)
            return;

        // The validity of the following assertion depends on
        // whether --string-non-empty is used
        if(nondet == 0) {
            assert arg1.length() > 0;
        } else if(nondet == 1) {
            assert arg2.length() > 0;
        } else if(nondet == 2) {
            // For this assertion to be valid, also need to limit the length of
            // strings because overflows could cause the sum to be negative.
            assert arg1.length() + arg2.length() > 1;
        } else {
            assert arg1.length() > 1;
        }
    }
}
