public class SyncTest {
  // Test that synchronized with null throws NullPointerException
  public static void testNull() {
    final Object o = null;
    try {
      synchronized (o) {
        assert false; // Should not reach here
      }
      assert false; // Should not reach here either
    }
    catch (NullPointerException e) {
      // Expected - this is the correct behavior
    }
  }

  // Test that synchronized with non-null object works
  public static void testNonNull() {
    final Object o = new Object();
    try {
      synchronized (o) {
        // Should execute normally
      }
    }
    catch (NullPointerException e) {
      assert false; // Should not throw for non-null object
    }
  }

  public static void main(String[] args) {
    testNull();
    testNonNull();
  }
}
