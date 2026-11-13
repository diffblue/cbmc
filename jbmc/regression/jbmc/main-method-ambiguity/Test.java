// Test case for GitHub issue #759
// CBMC should not produce CONVERSION ERROR when there are multiple
// methods named 'main' with different signatures.
// Only the method with signature void main(String[]) is a valid entry point.

public class Test {
    
    // Invalid main method - no parameters
    public static void main() {
    }
    
    // Valid main method - String[] parameter
    public static void main(String[] args) {
        assert false; // This should be the entry point
    }
    
    // Invalid main method - single String parameter
    public static void main(String arg) {
    }
}
