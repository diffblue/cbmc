public class boolean2
{
  public void entry(boolean b)
  {
    boolean result=f(b);
    assert result==!b;
  }

  public boolean f(boolean b)
  {
    return !b;
  }
}
