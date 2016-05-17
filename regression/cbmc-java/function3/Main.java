
class A
{
  public void dummy() {}

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

