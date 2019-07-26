public class Lambdatest {

  class A {
    int x;
  }

  CustomLambda<Integer> custom = x -> true;
  BiFunction<Float, Integer, Integer> add = (x0, y0) -> x0.intValue() + y0;
  int z = 10;

  A a = new A();
  B b = new B();

  public Integer captureNone(Float x, Integer y,
                             BiFunction<Float, Integer, Integer> fun) {
    return fun.apply(x, y);
  }

  public int captureReference(Float x, Integer y, Integer z) {
    Integer tmp = add.apply(x, y);
    Function<Integer, Integer> mul = (a) -> a * tmp;
    return mul.apply(z);
  }

  public int captureInt(int x) {
    int z = 5;
    Function<Integer, Integer> foo = (a) -> a * z;
    return foo.apply(x);
  }

  public int captureThisPrimitive(int x) {
    Function<Integer, Integer> foo = (a) -> a * z;
    return foo.apply(x);
  }

  public int captureThisReference(int x) {
    a.x = 10;

    Function<Integer, Integer> foo = (y) -> y * a.x;
    return foo.apply(x);
  }

  public int captureAndCall(int x) {
    b.y = 10;
    Function<Integer, Integer> foo = (y) -> {
      int r = y * b.y;
      b.set(r);
      return r;
    };
    b = new B();
    b.y = 14;
    return foo.apply(x);
  }

  public int captureAndAssign(int x) {
    b.y = 10;
    Function<Integer, Integer> foo = (y) -> {
      int r = y * b.y;
      b.y = r;
      return r;
    };
    return foo.apply(x);
  }

  // test static field of different class
  public double callStatic(Double x) { return B.dmul.apply(x); }

  public int capture2(Float a) { return add.apply(a, 1); }

  public boolean custom(Integer i) { return custom.is_ok(i); }

  public static void main(String[] args, int unknown) {
    Lambdatest lt = new Lambdatest();
    if (unknown == 0) {
      // should succeed
      assert lt.captureNone(1.0f, 2, (x, y) -> x.intValue() + y) == 3;
    } else if (unknown == 1) {
      // should fail
      assert lt.captureNone(1.0f, 2, (x, y) -> x.intValue() + y) == 4;
    } else if (unknown == 2) {
      assert lt.captureReference(1.0f, 2, 3) == 9; // should succeed
    } else if (unknown == 3) {
      assert lt.captureReference(1.0f, 2, 3) == 10; // should fail
    } else if (unknown == 4) {
      assert lt.captureInt(2) == 10; // should succeed
    } else if (unknown == 5) {
      assert lt.captureInt(2) == 11; // should fail
    } else if (unknown == 6) {
      assert lt.captureThisPrimitive(3) == 30; // should succeed
    } else if (unknown == 7) {
      assert lt.captureThisPrimitive(3) == 31; // should fail
    } else if (unknown == 8) {
      assert lt.captureThisReference(4) == 40; // should succeed
    } else if (unknown == 9) {
      assert lt.captureThisReference(4) == 41; // should fail
    } else if (unknown == 10) {
      assert lt.captureAndCall(5) == 70; // should succeed
      assert lt.b.y == 70;               // check side-effects of l method
    } else if (unknown == 11) {
      assert lt.captureAndCall(5) == 51; // should fail
    } else if (unknown == 12) {
      assert lt.captureAndAssign(6) == 60; // should succeed
      assert lt.b.y == 60;                 // check side-effects of m method
    } else if (unknown == 13) {
      assert lt.captureAndAssign(6) == 61; // should fail
    } else if (unknown == 14) {
      assert lt.callStatic(7.0) == 10.5; // should succeed
    } else if (unknown == 15) {
      assert lt.callStatic(7.0) == 12; // should fail
    } else if (unknown == 16) {
      assert lt.capture2(8.0f) == 9; // should succeed
    } else if (unknown == 17) {
      assert lt.capture2(8.0f) == 10; // should fail
    } else if (unknown == 18) {
      assert lt.custom(9); // should succeed
    } else if (unknown == 19) {
      assert !lt.custom(9); // should fail
      // Test array capture
    } else if (unknown == 20) {
      int array[] = new int[3];
      Function<Integer, Integer> func = (x) -> x + array.length;
      assert func.apply(2) == 5; // should succeed
    } else if (unknown == 21) {
      int array[] = new int[3];
      Function<Integer, Integer> func = (x) -> x + array.length;
      assert func.apply(2) == 6; // should fail
      // Test reference array
    } else if (unknown == 22) {
      Integer array[] = new Integer[3];
      Function<Integer, Integer> func = (x) -> x + array.length;
      assert func.apply(2) == 5; // should succeed
    } else if (unknown == 23) {
      Integer array[] = new Integer[3];
      Function<Integer, Integer> func = (x) -> x + array.length;
      assert func.apply(2) == 6; // should fail
      // Test outer class capture
    } else if (unknown == 24) {
      Outer outer = new Outer();
      outer.value = 42;
      Outer.Inner inner = outer.new Inner();
      Function<Integer, Integer> getter = inner.getOuterGetter();
      assert (getter.apply(0) == 42); // should succeed
    } else if (unknown == 25) {
      Outer outer = new Outer();
      outer.value = 42;
      Outer.Inner inner = outer.new Inner();
      Function<Integer, Integer> getter = inner.getOuterGetter();
      assert (getter.apply(0) != 42); // should fail
      // Static intialized lambda
    } else if (unknown == 26) {
      assert StaticLambdas.id.apply(96) == 96; // should succeed
    } else if (unknown == 27) {
      assert StaticLambdas.id.apply(96) != 96; // should fail
      // Reference equality of the captured object
    } else if (unknown == 28) {
      Object object = new Object();
      Function<Integer, Object> lambda = (x) -> object;
      assert (lambda.apply(0) == object); // should succeed
    } else if (unknown == 29) {
      Object object = new Object();
      Function<Integer, Object> lambda = (x) -> object;
      assert (lambda.apply(0) != object); // should fail
    }
  }

  static void lambdaCaptureNondet(Integer value) {
    Function<Integer, Integer> func = (x) -> value;
    assert func.apply(0) == 42;
  }
}

class StaticLambdas {
  final static Function<Integer, Integer> id = x -> x;
}

class Outer {
  int value;
  class Inner {
    Function<Integer, Integer> getOuterGetter() { return (x) -> value; }
  }
}

class C implements CustomLambda<Integer> {
  public boolean is_ok(Integer i) { return true; }
}
