class instanceof6
{
  public static void main(String[] args)
  {
    A[] as = { new A(), new B() };
    assert(as[0] instanceof A);
    assert(as[1] instanceof A);
  }
};

class A {
}

class B extends A {
}
