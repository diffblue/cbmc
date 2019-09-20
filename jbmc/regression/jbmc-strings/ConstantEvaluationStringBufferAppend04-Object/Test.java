public class Test
{
  public void testSuccess()
  {
    StringBuffer sb = new StringBuffer("abc");
    Integer i = new Integer(3);
    sb.append(i);
    assert sb.toString().equals("abc3");

    sb.append((Object)"xyz");
    assert sb.toString().equals("abc3xyz");

    sb.append((Object)null);
    assert sb.toString().equals("abc3xyznull");
  }

  public void testNoPropagation(Object obj)
  {
    StringBuffer sb = new StringBuffer();
    assert obj.toString().equals("");
  }
}
