class Gen<T> {
  public T t;
}

class IWrapper {
  public int i;
}

class BWrapper {
  public boolean b;
}

class TestClass {
  static void testFunction() {
    Gen<IWrapper> a = new Gen<>();
    Gen b = a;
    assert(b ==  a);
    Gen<BWrapper> c;
    c = b;
    assert(c == b);
    assert(c.equals(a));
  }

  static void testFunctionWithInput(Gen a, Gen<IWrapper> b, Gen<BWrapper> c) {
    if(a != null && b != null && c != null &&
      a.t != null && b.t != null && c.t != null)
    {
      b = a;
      assert(b == a);
      a = c;
      assert(a == c);
    }
  }
}
