import org.cprover.CProver;

class NondetCharSequence
{
  static void main()
  {
    CharSequence x = CProver.nondetWithNull(null);
    assert x == null || x instanceof CharSequence;
  }
}
