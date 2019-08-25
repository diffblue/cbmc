import org.cprover.CProver;

public class Test {

  public static void test() {

    String[][] stringArrays = new String[1][1];

    Object[] clone = CProver.createArrayWithType(1, stringArrays);
    assert clone instanceof String[][];
    assert clone.length == 1;
    assert clone[0] == null;
    assert clone instanceof Object[];
    assert clone instanceof String[]; // Should fail
  }
}
