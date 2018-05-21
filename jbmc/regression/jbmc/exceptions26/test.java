class A extends RuntimeException {}
class B extends A {}

// This test verifies that catches are executed in the correct order
public class test {
  public static void main (String args[]) {
    int i = 0;
    try {
      try {
        throw new A();
      }
      catch(A exc) {
        i++;
        throw new B();
      }
      finally
      {
        // Make sure A threw into the catch
        assert(i==1);
        i++;
      }
    }
    catch(B exc) {
      // Make sure finally was executed
      assert(i==2);
      i++;
    }
    // Make sure B was rethrown by finally
    assert(i==3);
  }
}
