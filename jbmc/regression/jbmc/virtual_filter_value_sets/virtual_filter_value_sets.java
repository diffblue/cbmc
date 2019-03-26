class A {
  public int f() { return 1; }
};

class B extends A {
  public int flag;

  public int f() { return flag; }
};

class Container {
  public A a_field;
}

class virtual_filter_value_sets {
  public static void test_without_deref(boolean nondet_bool) {
    A a = new A();

    B b = new B();
    b.flag = 9;

    A a_or_b = nondet_bool ? a : b;
    int retval = a_or_b.f();

    assert false;
  }

  public static void test_with_deref(boolean nondet_bool) {
    A a = new A();

    B b = new B();
    b.flag = 9;

    Container c = new Container();
    c.a_field = nondet_bool ? a : b;
    int retval = c.a_field.f();

    assert false;
  }
}
