import org.cprover.CProverString;

public class Test
{
  public void testSuccess1()
  {
    StringBuffer sb = new StringBuffer("abc");
    CProverString.setLength(sb, 0);
    assert sb.toString().equals("");
  }

  public void testSuccess2()
  {
    StringBuffer sb = new StringBuffer("abc");
    CProverString.setLength(sb, 2);
    assert sb.toString().equals("ab");
  }

  public void testSuccess3()
  {
    StringBuffer sb = new StringBuffer("abc");
    CProverString.setLength(sb, 3);
    assert sb.toString().equals("abc");
  }

  public void testSuccess4()
  {
    StringBuffer sb = new StringBuffer("abc");
    CProverString.setLength(sb, 4);
    assert sb.toString().equals("abc\u0000");
  }

  public void testSuccess5()
  {
    StringBuffer sb = new StringBuffer("abc");
    CProverString.setLength(sb, 5);
    assert sb.toString().equals("abc\u0000\u0000");
  }

  public void testSuccess6(StringBuffer sb)
  {
    CProverString.setLength(sb, 0);
    assert sb.toString().equals("");
  }

  public void testNoPropagation1()
  {
    StringBuffer sb = new StringBuffer("abc");
    CProverString.setLength(sb, -1);
    assert sb.toString().equals("abc");
  }

  public void testNoPropagation2(StringBuffer sb)
  {
    CProverString.setLength(sb, 3);
    assert sb.toString().equals("abc");
  }

  public void testNoPropagation3(int newLength)
  {
    StringBuffer sb = new StringBuffer("abc");
    CProverString.setLength(sb, newLength);
    assert sb.toString().equals("abc");
  }
}
