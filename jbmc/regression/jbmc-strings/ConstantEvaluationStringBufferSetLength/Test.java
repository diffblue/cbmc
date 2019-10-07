public class Test
{
  public void testSuccess1()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.setLength(0);
    assert sb.toString().equals("");
  }

  public void testSuccess2()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.setLength(2);
    assert sb.toString().equals("ab");
  }

  public void testSuccess3()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.setLength(3);
    assert sb.toString().equals("abc");
  }

  public void testSuccess4()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.setLength(4);
    assert sb.toString().equals("abc\u0000");
  }

  public void testSuccess5()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.setLength(5);
    assert sb.toString().equals("abc\u0000\u0000");
  }

  public void testSuccess6(StringBuffer sb)
  {
    sb.setLength(0);
    assert sb.toString().equals("");
  }

  public void testException()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.setLength(-1);
  }

  public void testNoPropagation1(StringBuffer sb)
  {
    sb.setLength(3);
    assert sb.toString().equals("abc");
  }

  public void testNoPropagation2(int newLength)
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.setLength(newLength);
    assert sb.toString().equals("abc");
  }
}
