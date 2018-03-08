// Helper classes
class Wrapper<T> {
  public T field;
}

class IntWrapper {
  public int i;
}

class TwoWrapper<K, V> {
  public K first;
  public V second;
}

interface InterfaceWrapper<T> {
  public T method(T t);
}

// A class extending a generic class instantiated with a standard library class
class SuperclassInst extends Wrapper<Integer> {
  public void foo() {
    this.field = 5;
  }
}

// A class extending a generic class instantiated with a user-defined class
class SuperclassInst2 extends Wrapper<IntWrapper> {
  public void foo() {
    this.field.i = 5;
  }
}

// A class extending an instantiated nested generic class
class SuperclassInst3 extends Wrapper<Wrapper<IntWrapper>> {
  public void foo() {
    this.field.field.i = 5;
  }
}

// A generic class extending a generic class (must be with the same parameter)
class SuperclassUninst<U> extends Wrapper<U> {
  public void foo(U value) {
    this.field = value;
  }
}
class SuperclassUninstTest
{
  SuperclassUninst<Integer> f;
  public void foo() {
    f.foo(new Integer(1));
  }
}


// A generic class extending a generic class with both instantiated and
// uninstantiated parameters
class SuperclassMixed<U> extends TwoWrapper<U,IntWrapper> {
  public void foo(U value) {
    this.first = value;
    this.second.i = 5;
  }
}
class SuperclassMixedTest
{
  SuperclassMixed<Boolean> f;
  public void foo() {
    f.foo(true);
  }
}

// Inner classes (generic or not) extending generic classes
class SuperclassInnerInst {
  class Inner extends Wrapper<Integer> {
    public void foo() {
      this.field = 5;
    }
  }
  public Inner inner;

  class InnerGen<T> extends Wrapper<T> {
    public void foo(T value) {
      this.field = value;
    }
  }
  public InnerGen<Boolean> inner_gen;

  public void foo() {
    inner.foo();
    inner_gen.foo(true);
  }
}

// Implicitly generic inner classes (generic or not) extending generic classes
class SuperclassInnerUninst<U> {
  class Inner extends Wrapper<U> {
    public void foo(U value) {
      this.field = value;
    }
  }
  public Inner inner;

  class InnerGen<T> extends TwoWrapper<U,T> {
    public void foo(U uvalue, T tvalue) {
      this.first = uvalue;
      this.second = tvalue;
    }
  }
  public InnerGen<Boolean> inner_gen;

  class InnerThree extends Inner {
  }
  public InnerThree inner_three;
}
class SuperclassInnerUninstTest
{
  SuperclassInnerUninst<IntWrapper> f;
  public void foo() {
    IntWrapper x = new IntWrapper();
    f.inner.foo(x);
    f.inner_gen.foo(x,true);
    f.inner_three.foo(x);
  }
}
