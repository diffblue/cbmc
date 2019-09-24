public class Test
{
  public void testSuccess()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.deleteCharAt(1);
    assert sb.toString().equals("ac");
  }

  public void testNoPropagation(int index)
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.deleteCharAt(index);
    assert sb.toString().equals("ac");
  }

  public void testIndexOutOfBounds1()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.deleteCharAt(-1);
    assert sb.toString().equals("ac");
  }

  public void testIndexOutOfBounds2()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.deleteCharAt(3);
    assert sb.toString().equals("ac");
  }
}
