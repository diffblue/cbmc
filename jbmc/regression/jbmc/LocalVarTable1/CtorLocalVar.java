public class CtorLocalVar 
{
  public CtorLocalVar()
  {
    String s2 = new String("foo");
    assert(true);
  }

  public CtorLocalVar test()
  {
    return new CtorLocalVar();
  }
}
