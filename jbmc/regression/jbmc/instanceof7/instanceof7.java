class instanceof7
{
  public static void main(String[] args)
  {
    A[] as = { new A(), new B() };
    assert(!(as[0] instanceof B));
    assert(as[1] instanceof B);
  }
};

class A {
}

class B extends A {
}
