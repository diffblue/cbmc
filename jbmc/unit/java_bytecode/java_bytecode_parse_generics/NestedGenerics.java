public class NestedGenerics
{
  Generic<Generic<Interface_Implementation>> field;
  Generic<Generic<Integer>> field2;

  Generic<Generic<Generic<Interface_Implementation>>> field3;
  Generic<Generic<Generic<Integer>>> field4;

  Generic<GenericTwoParam<Interface_Implementation,Interface_Implementation>> field5;
  Generic<GenericTwoParam<Interface_Implementation,Integer>> field6;
  Generic<GenericTwoParam<Integer,Integer>> field7;

  GenericTwoParam<Generic<Interface_Implementation>, Generic<Interface_Implementation>> field8;
  GenericTwoParam<Generic<Interface_Implementation>, Generic<Integer>> field9;
  GenericTwoParam<Generic<Integer>, Generic<Integer>> field10;

  GenericTwoParam<Generic<Integer>, Interface_Implementation> field11;
  GenericTwoParam<Generic<Generic<Integer>>, Interface_Implementation> field12;

  GenericTwoParam<GenericTwoParam<Interface_Implementation,Integer>, Generic<Integer>> field13;

  void method(Generic<Generic<Interface_Implementation>> input)
  {

  }

  void method2(Generic<Generic<Integer>> input)
  {

  }

  void method3(Generic<Generic<Generic<Interface_Implementation>>> input)
  {

  }

  void method4(Generic<Generic<Generic<Integer>>> input)
  {

  }

  void method5(Generic<GenericTwoParam<Interface_Implementation,Interface_Implementation>> input)
  {

  }

  void method6(Generic<GenericTwoParam<Interface_Implementation,Integer>> input)
  {

  }

  void method7(Generic<GenericTwoParam<Integer,Integer>> input)
  {

  }

  void method8(GenericTwoParam<Generic<Interface_Implementation>, Generic<Interface_Implementation>> input)
  {

  }

  void method9(GenericTwoParam<Generic<Interface_Implementation>, Generic<Integer>> input)
  {

  }

  void method10(GenericTwoParam<Generic<Integer>, Generic<Integer>> input)
  {

  }

  void method11(GenericTwoParam<Generic<Integer>, Interface_Implementation> input)
  {

  }
  void method12(GenericTwoParam<Generic<Generic<Integer>>, Interface_Implementation> input)
  {

  }

  void method13(GenericTwoParam<GenericTwoParam<Interface_Implementation,Integer>, Generic<Integer>> input)
  {

  }


  Generic<Generic<Interface_Implementation>> ret_method()
  {
    return null;
  }

  Generic<Generic<Integer>> ret_method2()
  {
    return null;
  }

  Generic<Generic<Generic<Interface_Implementation>>> ret_method3()
  {
    return null;
  }

  Generic<Generic<Generic<Integer>>> ret_method4()
  {
    return null;
  }

  Generic<GenericTwoParam<Interface_Implementation,Interface_Implementation>> ret_method5()
  {
    return null;
  }

  Generic<GenericTwoParam<Interface_Implementation,Integer>> ret_method6()
  {
    return null;
  }

  Generic<GenericTwoParam<Integer,Integer>> ret_method7()
  {
    return null;
  }

  GenericTwoParam<Generic<Interface_Implementation>, Generic<Interface_Implementation>> ret_method8()
  {
    return null;
  }

  GenericTwoParam<Generic<Interface_Implementation>, Generic<Integer>> ret_method9()
  {
    return null;
  }

  GenericTwoParam<Generic<Integer>, Generic<Integer>> ret_method10()
  {
    return null;
  }

  GenericTwoParam<Generic<Integer>, Interface_Implementation> ret_method11()
  {
    return null;
  }

  GenericTwoParam<Generic<Generic<Integer>>, Interface_Implementation> ret_method12()
  {
    return null;
  }

  GenericTwoParam<GenericTwoParam<Interface_Implementation,Integer>, Generic<Integer>> ret_method13()
  {
    return null;
  }

}
