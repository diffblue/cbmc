class A extends RuntimeException {}
class B extends A {}

public class Test {
  void foo()
  {
    A a=new A();
    throw a;
  }
  void goo()
  {
    try
    {
      foo();
      assert false;
    }
    catch(B e)
    {
      assert false;
    } 
  }
  
}
