public class Test {
  public String check(int assertId) {
    Object o;
    o = "foo";
    String classId = org.cprover.CProver.classIdentifier(o);
    if(assertId == 1) {
      assert org.cprover.CProverString.equals(classId, "java.lang.String");
    } else if(assertId == 2) {
      assert org.cprover.CProverString.equals(classId, "java.lang.Integer");
    }
    o = new Integer(42);
    classId = org.cprover.CProver.classIdentifier(o);
    if(assertId == 3) {
      assert org.cprover.CProverString.equals(classId, "java.lang.String");
    } else if(assertId == 4) {
      assert org.cprover.CProverString.equals(classId, "java.lang.Integer");
    }
    return classId;
  }
}
