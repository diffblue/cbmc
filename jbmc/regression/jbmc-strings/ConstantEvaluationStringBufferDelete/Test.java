public class Test
{
  public void testSuccess1()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.delete(0, 0);
    assert sb.toString().equals("abc");
  }

  public void testSuccess2()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.delete(0, 3);
    assert sb.toString().equals("");
  }

  public void testSuccess3()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.delete(0, 4);
    assert sb.toString().equals("");
  }

  public void testSuccess4()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.delete(1, 2);
    assert sb.toString().equals("ac");
  }

  public void testSuccess5()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.delete(3, 4);
    assert sb.toString().equals("abc");
  }

  public void testNoPropagation1(int index)
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.delete(index, 3);
    assert sb.toString().equals("ac");
  }

  public void testNoPropagation2(int index)
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.delete(0, index);
    assert sb.toString().equals("ac");
  }

  public void testIndexOutOfBounds1()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.delete(-1, 3);
  }

  public void testIndexOutOfBounds2()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.delete(4, 5);
  }

  public void testIndexOutOfBounds3()
  {
    StringBuffer sb = new StringBuffer("abc");
    sb.delete(2, 1);
  }
}
