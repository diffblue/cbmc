public class Test
{
  public void testSuccess()
  {
    StringBuilder sb = new StringBuilder("abc");
    sb.deleteCharAt(1);
    assert sb.toString().equals("ac");
  }

  public void testNoPropagation(int index)
  {
    StringBuilder sb = new StringBuilder("abc");
    sb.deleteCharAt(index);
    assert sb.toString().equals("ac");
  }

  public void testIndexOutOfBounds1()
  {
    StringBuilder sb = new StringBuilder("abc");
    sb.deleteCharAt(-1);
    assert sb.toString().equals("ac");
  }

  public void testIndexOutOfBounds2()
  {
    StringBuilder sb = new StringBuilder("abc");
    sb.deleteCharAt(3);
    assert sb.toString().equals("ac");
  }
}
