
class A
{
  public void dummy()
  {
    // check some setup
    assert this instanceof A;
  }

  public B b;
}

class B
{
  public A a;
}


public class Main
{
  public static void main(String[] args)
  {
    B B = new B();
  }
}

