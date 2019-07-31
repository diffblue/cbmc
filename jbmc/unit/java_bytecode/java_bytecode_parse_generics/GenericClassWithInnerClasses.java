class GenericClassWithInnerClasses<T>
{
  class Inner {
    T t1;
    Generic<T> t2;

    class InnerInner {
      T tt1;
      Generic<Generic<T>> tt2;
    }
  }

  class GenericInner<U> {
    T gt1;
    GenericTwoParam<T,U> gt2;

    class GenericInnerInner<V>{

    }

    class ShadowingGenericInner<U> {
      U shadowedField;
    }

    ShadowingGenericInner<String> shadowingField;
  }

  static class StaticInner<U>{
    U st;
  }

  Inner f1;
  Inner.InnerInner f2;
  GenericInner<Integer> f3;
}
