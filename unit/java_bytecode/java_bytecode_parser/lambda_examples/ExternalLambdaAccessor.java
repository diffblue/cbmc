class ExternalLambdas
{
  int memberPrimitive;
  Object memberReference;
  DummyGeneric<Integer> memberSpecalisedGeneric;

  public SimpleLambda simpleLambda = () -> { /*NOP*/ };
  public ParameterLambda paramLambda = (int primitive, Object reference, DummyGeneric<Integer> specalisedGeneric) -> {};
  public ArrayParameterLambda arrayParamLambda = (int[] primitive, Object[] reference, DummyGeneric<Integer>[] specalisedGeneric) -> {};
  public ReturningLambdaPrimitive returnPrimitiveLambda = () -> { return 1; };
  public ReturningLambdaReference returnReferenceLambda = () -> { return null; };
  public ReturningLambdaSpecalisedGeneric returningSpecalisedGenericLambda = () -> { return null; };
  public ReturningLambdaPrimitiveArray returnPrimitiveArrayLambda = () -> { return null; };
  public ReturningLambdaReferenceArray returnReferenceArrayLambda = () -> { return null; };
  public ReturningLambdaSpecalisedGenericArray returningSpecalisedGenericArrayLambda = () -> { return null; };
  public ReturningLambdaPrimitive returnPrimitiveLambdaCapture = () -> { return memberPrimitive; };
  public ReturningLambdaReference returnReferenceLambdaCapture = () -> { return memberReference; };
  public ReturningLambdaSpecalisedGeneric returningSpecalisedGenericLambdaCapture = () -> { return memberSpecalisedGeneric; };
}

public class ExternalLambdaAccessor
{
  public static void test()
  {
    ExternalLambdas e = new ExternalLambdas();
    e.simpleLambda.Execute();
    e.paramLambda.Execute(4, null, null);
    e.arrayParamLambda.Execute(null, null, null);
    e.returnPrimitiveLambda.Execute();
    e.returnReferenceLambda.Execute();
    e.returningSpecalisedGenericLambda.Execute();
    e.returnPrimitiveArrayLambda.Execute();
    e.returnReferenceArrayLambda.Execute();
    e.returningSpecalisedGenericArrayLambda.Execute();
    e.returnPrimitiveLambdaCapture.Execute();
    e.returnReferenceLambdaCapture.Execute();
    e.returningSpecalisedGenericLambdaCapture.Execute();
  }
}
