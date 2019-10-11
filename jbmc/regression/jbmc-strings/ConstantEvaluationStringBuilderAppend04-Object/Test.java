public class Test
{
  public void testSuccess()
  {
    StringBuilder sb = new StringBuilder("abc");
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
    StringBuilder sb = new StringBuilder();
    assert obj.toString().equals("");
  }
}
