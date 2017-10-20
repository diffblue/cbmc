public class GenericClass<T>
{
  class InnerClass
  {
  }

  class GenericInnerClass<V>
  {
    V field;

    class DoublyNestedInnerClass
    {

    }

    class DoublyNestedInnerGemericClass<U>
    {
      T field;
    }
  }

  class SameGenericParamInnerClass<T>
  {
    T field;
  }

  InnerClass field;
  GenericInnerClass<Foo> field2;
  SameGenericParamInnerClass<Foo> field3;

  GenericInnerClass<T> field4;
  SameGenericParamInnerClass<T> field5;
}