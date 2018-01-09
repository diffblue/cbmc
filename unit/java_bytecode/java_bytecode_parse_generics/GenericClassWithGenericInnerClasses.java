public class GenericClassWithGenericInnerClasses<T>
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

  class TwoParamInnerClass<K, L>
  {
    K k;
    L l;
  }

  InnerClass field;

  GenericInnerClass<Interface_Implementation> field2;
  GenericInnerClass<T> field3;

  GenericInnerClass<Interface_Implementation>.DoublyNestedInnerClass field4;
  GenericInnerClass<T>.DoublyNestedInnerClass field5;

  GenericInnerClass<Interface_Implementation>.DoublyNestedInnerGenericClass<Interface_Implementation> field6;
  GenericInnerClass<T>.DoublyNestedInnerGenericClass<T> field7;

  TwoParamInnerClass<Interface_Implementation,Interface_Implementation> field8;
  TwoParamInnerClass<Interface_Implementation,T> field9;
  TwoParamInnerClass<T,T> field10;

  GenericInnerClass<GenericClassWithGenericInnerClasses<Integer>>.DoublyNestedInnerGenericClass<T>  field11;

  void method(InnerClass input)
  {

  }

  void method2(InnerClass input, InnerClass input2)
  {

  }


  void method3(GenericInnerClass<Interface_Implementation> input)
  {

  }

  void method4(GenericInnerClass<T> input)
  {

  }

  void method5(GenericInnerClass<Interface_Implementation>.DoublyNestedInnerClass input)
  {

  }

  void method6(GenericInnerClass<T>.DoublyNestedInnerClass input)
  {

  }

  void method7(GenericInnerClass<Interface_Implementation>.DoublyNestedInnerGenericClass<Interface_Implementation> input)
  {

  }

  void method8(GenericInnerClass<T>.DoublyNestedInnerGenericClass<T> input)
  {

  }

  void method9(TwoParamInnerClass<Interface_Implementation,Interface_Implementation> input)
  {

  }

  void method10(TwoParamInnerClass<Interface_Implementation,T> input)
  {

  }

  void method11(TwoParamInnerClass<T,T> input)
  {

  }

  InnerClass ret_method1()
  {
    return null;
  }

  GenericInnerClass<Interface_Implementation> ret_method2()
  {
    return null;
  }

  GenericInnerClass<T> ret_method3()
  {
    return null;
  }

  GenericInnerClass<Interface_Implementation>.DoublyNestedInnerClass ret_method4()
  {
    return null;
  }
  GenericInnerClass<T>.DoublyNestedInnerClass ret_method5()
  {
    return null;
  }
  GenericInnerClass<Interface_Implementation>.DoublyNestedInnerGenericClass<Interface_Implementation> ret_method6()
  {
    return null;
  }
  GenericInnerClass<T>.DoublyNestedInnerGenericClass<T> ret_method7()
  {
    return null;
  }
  TwoParamInnerClass<Interface_Implementation,Interface_Implementation> ret_method8()
  {
    return null;
  }
  TwoParamInnerClass<Interface_Implementation,T> ret_method9()
  {
    return null;
  }
  TwoParamInnerClass<T,T> ret_method10()
  {
    return null;
  }
}
