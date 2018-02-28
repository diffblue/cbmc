public class MemberLambdas {

  int memberPrimitive;
  Object memberReference;
  DummyGeneric<Integer> memberSpecalisedGeneric;

  SimpleLambda simpleLambda = () -> { /*NOP*/ };
  ParameterLambda paramLambda = (int primitive, Object reference, DummyGeneric<Integer> specalisedGeneric) -> {};
  ArrayParameterLambda arrayParamLambda = (int[] primitive, Object[] reference, DummyGeneric<Integer>[] specalisedGeneric) -> {};
  ReturningLambdaPrimitive returnPrimitiveLambda = () -> { return 1; };
  ReturningLambdaReference returnReferenceLambda = () -> { return null; };
  ReturningLambdaSpecalisedGeneric returningSpecalisedGenericLambda = () -> { return null; };
  ReturningLambdaPrimitiveArray returnPrimitiveArrayLambda = () -> { return null; };
  ReturningLambdaReferenceArray returnReferenceArrayLambda = () -> { return null; };
  ReturningLambdaSpecalisedGenericArray returningSpecalisedGenericArrayLambda = () -> { return null; };

  ReturningLambdaPrimitive returnPrimitiveLambdaCapture = () -> { return memberPrimitive; };
  ReturningLambdaReference returnReferenceLambdaCapture = () -> { return memberReference; };
  ReturningLambdaSpecalisedGeneric returningSpecalisedGenericLambdaCapture = () -> { return memberSpecalisedGeneric; };


  public void testMethod() {
    simpleLambda.Execute();
    paramLambda.Execute(4, null, null);
    arrayParamLambda.Execute(null, null, null);
    returnPrimitiveLambda.Execute();
    returnReferenceLambda.Execute();
    returningSpecalisedGenericLambda.Execute();
    returnPrimitiveArrayLambda.Execute();
    returnReferenceArrayLambda.Execute();
    returningSpecalisedGenericArrayLambda.Execute();

    returnPrimitiveLambdaCapture.Execute();
    returnReferenceLambdaCapture.Execute();
    returningSpecalisedGenericLambdaCapture.Execute();
  }
}

