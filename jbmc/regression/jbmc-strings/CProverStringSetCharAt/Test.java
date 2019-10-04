import org.cprover.CProverString;

public class Test
{
  public void test1(int index)
  {
    StringBuffer sb = new StringBuffer("abc");
    CProverString.setCharAt(sb, index, 'd');
    assert sb.toString().equals("abc");
  }

  public void test2()
  {
    StringBuffer sb = new StringBuffer("abc");
    CProverString.setCharAt(sb, -1, 'd');
    assert sb.toString().equals("abc");
  }

  public void test3()
  {
    StringBuffer sb = new StringBuffer("abc");
    CProverString.setCharAt(sb, 3, 'd');
    assert sb.toString().equals("abc");
  }

  public void test4(boolean b)
  {
    StringBuffer sb = new StringBuffer("abc");
    int i = b ? 1 : 2;
    CProverString.setCharAt(sb, i, 'd');
    String s = sb.toString();
    assert !b || s.equals("adc");
    assert b || s.equals("abd");
  }
}
