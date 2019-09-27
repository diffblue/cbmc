import org.cprover.CProverString;

public class Test
{
  public void testSuccess1()
  {
    StringBuffer sb = new StringBuffer("abc");
    CProverString.setCharAt(sb, 0, 'd');
    assert sb.toString().equals("dbc");
  }

  public void testSuccess2()
  {
    StringBuffer sb = new StringBuffer("abc");
    CProverString.setCharAt(sb, 2, 'd');
    assert sb.toString().equals("abd");
  }

  public void testNoPropagation1()
  {
    StringBuffer sb = new StringBuffer("abc");
    CProverString.setCharAt(sb, -1, 'd');
    assert sb.toString().equals("dbc");
  }

  public void testNoPropagation2()
  {
    StringBuffer sb = new StringBuffer("abc");
    CProverString.setCharAt(sb, 3, 'd');
    assert sb.toString().equals("dbc");
  }

  public void testNoPropagation3(StringBuffer sb)
  {
    CProverString.setCharAt(sb, 1, 'd');
    assert sb.toString().equals("dbc");
  }

  public void testNoPropagation4(int index)
  {
    StringBuffer sb = new StringBuffer("abc");
    CProverString.setCharAt(sb, index, 'd');
    assert sb.toString().equals("dbc");
  }
}
