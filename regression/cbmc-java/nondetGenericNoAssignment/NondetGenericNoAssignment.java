import org.cprover.CProver;

class NondetGenericNoAssignment
{
  static void callWithoutAssignment()
  {
    assert CProver.nondet() == null;
  }
}
