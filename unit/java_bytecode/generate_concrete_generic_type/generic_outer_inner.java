public class generic_outer_inner
{
  class GenericOuter<T>
  {
    class Inner {
      T f1;
      Integer f2;

      class InnerInner {
        T f1;
      }
    }

    class GenericInner<U>
    {

    }

    T f1;
    Inner f2;
    GenericInner<String> f3;
  }

  class Outer
  {
    class Inner
    {
      class GenericInnerInner<T>
      {
        T f1;
      }
    }

    class GenericInner<T>
    {
      class InnerInner
      {
        T f1;
      }

      class GenericInnerInner<U>
      {
        T f1;
        U f2;
      }

      GenericInnerInner<String> f1;
    }

    class TwoParamGenericInner<U,V>
    {
      class InnerInner
      {
        U f1;
        V f2;
      }

      U f1;
      V f2;
    }
  }

  GenericOuter<Integer> t1;
  GenericOuter<Integer>.Inner t2;
  GenericOuter<Integer[]>.Inner t2a;
  GenericOuter<String>.Inner.InnerInner t3;
  GenericOuter<String[]>.Inner.InnerInner t3a;
  GenericOuter<String>.GenericInner<Integer> t4;

  Outer.Inner.GenericInnerInner<Integer> t5;
  Outer.GenericInner<Integer> t6;
  Outer.GenericInner<Integer>.InnerInner t7;
  Outer.GenericInner<Integer[]>.InnerInner t7a;
  Outer.GenericInner<Integer>.GenericInnerInner<String> t8;

  Outer.TwoParamGenericInner<Integer, String> t9;
  Outer.TwoParamGenericInner<Integer, String>.InnerInner t10;
  Outer.TwoParamGenericInner<Integer[], String[]>.InnerInner t10a;

  GenericOuter<Outer> t11;
}

