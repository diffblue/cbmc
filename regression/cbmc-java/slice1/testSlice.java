class test
{
  public void f1()
  {
    int y=0;
    y++;
  }

  public void f2()
  {
    i++;
  }

  public int f3()
  {
    return i;
  }

  private int i;
}

public class testSlice
{
  public static void main(String[] args)
  {
    test t = new test();
    t.f1();
    t.f2();
    assert t.f3()==1;
  }
}
