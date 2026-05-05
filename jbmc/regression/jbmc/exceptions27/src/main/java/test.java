import org.cprover.CProver;
class A extends RuntimeException {}
class B extends A {}

// This test verifies that catches are executed in the correct order
public class test {
  public static void main (String args[]) {
    int i = 0;
    int j = 0;
    try {
      try {
        try {
          if (CProver.nondetBoolean()) throw new A();
          else throw new B();
        }
        catch(B exc) {
          i++;
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
        assert(i==2);
        // Account for the rethrow in finally
        j++;
      }
      catch(B exc) {
        // Make sure finally was executed
        assert(i==2);
        i++;
        throw new B();
      }
      finally 
      {
        assert ((i+j) == 3);
      }
      // Account for the rethrow in finally
      j++;
    }
    catch(B exc)
    {
      i++;
    }
    // Make sure B was rethrown by finally when A was thrown
    // or if B was thrown there was no rethrow
    assert(i+j == 4);
  }
}
