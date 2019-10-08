public class Test
{
  public void testSuccess1()
  {
    StringBuilder sb = new StringBuilder("abc");
    sb.setCharAt(0, 'd');
    assert sb.toString().equals("dbc");
  }

  public void testSuccess2()
  {
    StringBuilder sb = new StringBuilder("abc");
    sb.setCharAt(2, 'd');
    assert sb.toString().equals("abd");
  }

  public void testException1()
  {
    StringBuilder sb = new StringBuilder("abc");
    sb.setCharAt(-1, 'd');
  }

  public void testException2()
  {
    StringBuilder sb = new StringBuilder("abc");
    sb.setCharAt(3, 'd');
  }

  public void testNoPropagation1(StringBuilder sb)
  {
    sb.setCharAt(1, 'd');
    assert sb.toString().equals("dbc");
  }

  public void testNoPropagation2(int index)
  {
    StringBuilder sb = new StringBuilder("abc");
    sb.setCharAt(index, 'd');
    assert sb.toString().equals("dbc");
  }
}
