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
  GenericInnerClass<T> field3;

  void method(InnerClass input)
  {

  }

  void method2(InnerClass input, InnerClass input2)
  {

  }


  void method3(GenericInnerClass<Foo> input)
  {

  }

  void method4(GenericInnerClass<T> input)
  {

  }

  InnerClass ret_method1()
  {
    return null;
  }

  GenericInnerClass<Foo> ret_method2()
  {
    return null;
  }

  GenericInnerClass<T> ret_method3()
  {
    return null;
  }
}
