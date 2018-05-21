import org.cprover.CProver;

class NondetChar
{
  static void main()
  {
    char x = CProver.nondetChar();
    assert x == '\0';
  }
}
