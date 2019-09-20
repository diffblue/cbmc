import org.cprover.other.MyOther;
import org.cprover.other.Parent;
import org.cprover.other.Child;

public class ExcludedProperties {

  public static void parameters() {
    int i = MyOther.identity(21);
    assert (i == 21);
  }

  public static void compileTimeReturnType() {
    Parent p = MyOther.subclass();
    assert (p == null || p instanceof Parent);
    if (p == null) {
      assert false; // reachable with "return nondet" body
    } else {
      if (p.num() == 1) {
        assert false; // reachable with "return nondet" body
      } else {
        assert false; // reachable with "return nondet" body
      }
    }
  }

  public static void runtimeReturnType() {
    Parent p = MyOther.subclass();
    assert (p == null || p instanceof Child);
  }
}
