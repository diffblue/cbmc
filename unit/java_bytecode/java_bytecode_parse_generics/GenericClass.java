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

    class DoublyNestedInnerGenericClass<U>
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

  GenericInnerClass<Foo>.DoublyNestedInnerClass field4;
  GenericInnerClass<T>.DoublyNestedInnerClass field5;

  GenericInnerClass<Foo>.DoublyNestedInnerGenericClass<Foo> field6;
  GenericInnerClass<T>.DoublyNestedInnerGenericClass<T> field7;

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

  void method5(GenericInnerClass<Foo>.DoublyNestedInnerClass input)
  {

  }

  void method6(GenericInnerClass<T>.DoublyNestedInnerClass input)
  {

  }

  void method7(GenericInnerClass<Foo>.DoublyNestedInnerGenericClass<Foo> input)
  {

  }

  void method8(GenericInnerClass<T>.DoublyNestedInnerGenericClass<T> input)
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

  GenericInnerClass<Foo>.DoublyNestedInnerClass ret_method4()
  {
    return null;
  }
  GenericInnerClass<T>.DoublyNestedInnerClass ret_method5()
  {
    return null;
  }
  GenericInnerClass<Foo>.DoublyNestedInnerGenericClass<Foo> ret_method6()
  {
    return null;
  }
  GenericInnerClass<T>.DoublyNestedInnerGenericClass<T> ret_method7()
  {
    return null;
  }
}
