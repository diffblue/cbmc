import org.cprover.CProver;

public class Test {

  public static void test() {

    String[] strings = new String[0];

    Object[] clone = CProver.createArrayWithType(1, strings);
    assert clone instanceof String[];
    assert clone.length == 1;
    assert clone[0] == null;
    assert clone instanceof Object[];
    assert clone instanceof Integer[]; // Should fail
  }
}
