public class static_init_order
{
  // as per the Java Virtual Machine Specification,
  // section 5.5, p. 35 we expect the static initializer of
  // the parent class to be called before the static initializer
  // of the class in question.
  //
  // The following tests will verify the aforementioned behaviour.

  public static void test1()
  {
    C object2 = new C();
    B object  = new B();
    if(object2.x != 20)
        // order of init is: C.clint, B.clint, A.clint
        // This should not be reachable as expected order
        // should be: C.clint, A.clint, B.clint.
        assert(false);
  }

  public static void test2()
  {
    C object2 = new C();
    B object  = new B();
    // Assertion is expected to fail,
    // as the only way for object2.x
    // to be assigned a value of 10 is through
    // the following incorrect ordering of init calls:
    // C.clint, B.clint, A.clint
    assert(object2.x == 10);
  }
}

class C
{
  public static int x = 0;
}

class A
{
  static {
    C.x=10;
  }
}

class B extends A
{
  static {
    C.x=20;
  }
}
