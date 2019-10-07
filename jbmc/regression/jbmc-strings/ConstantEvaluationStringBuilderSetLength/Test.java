public class Test
{
  public void testSuccess1()
  {
    StringBuilder sb = new StringBuilder("abc");
    sb.setLength(0);
    assert sb.toString().equals("");
  }

  public void testSuccess2()
  {
    StringBuilder sb = new StringBuilder("abc");
    sb.setLength(2);
    assert sb.toString().equals("ab");
  }

  public void testSuccess3()
  {
    StringBuilder sb = new StringBuilder("abc");
    sb.setLength(3);
    assert sb.toString().equals("abc");
  }

  public void testSuccess4()
  {
    StringBuilder sb = new StringBuilder("abc");
    sb.setLength(4);
    assert sb.toString().equals("abc\u0000");
  }

  public void testSuccess5()
  {
    StringBuilder sb = new StringBuilder("abc");
    sb.setLength(5);
    assert sb.toString().equals("abc\u0000\u0000");
  }

  public void testSuccess6(StringBuilder sb)
  {
    sb.setLength(0);
    assert sb.toString().equals("");
  }

  public void testException()
  {
    StringBuilder sb = new StringBuilder("abc");
    sb.setLength(-1);
  }

  public void testNoPropagation1(StringBuilder sb)
  {
    sb.setLength(3);
    assert sb.toString().equals("abc");
  }

  public void testNoPropagation2(int newLength)
  {
    StringBuilder sb = new StringBuilder("abc");
    sb.setLength(newLength);
    assert sb.toString().equals("abc");
  }
}
