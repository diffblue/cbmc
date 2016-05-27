
class A
{
  public int i;
}

class B extends A
{
  public int j;
}

class C extends B
{
  public int k;
}

class D
{
  protected C c;

  public void fail()
  {
    assert c.i == 0 || c.j == 0 || c.k == 0;
  }
}

public class Main
{
  public static void main(String[] args)
  {
    D d = new D();
  }
}

