interface I
{
  void interface_method();
}

abstract class A
{
  abstract void method();

  int i;
}

class C
{

  int j;
  void concreteMethod() {

  }
}

class Extender extends A {
  void method() {

  }
}

class Implementor implements I {
  public void interface_method(){

  }
}