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

  InnerClass method5()
  {
    return null;
  }

  GenericInnerClass<Foo> method6()
  {
    return null;
  }

  GenericInnerClass<T> method7()
  {
    return null;
  }
}
