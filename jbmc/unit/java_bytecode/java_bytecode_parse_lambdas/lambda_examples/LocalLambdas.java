public class LocalLambdas {
  public static void test() {
    int localPrimitive = 5;
    Object localReference = null;
    DummyGeneric<Integer> localSpecalisedGeneric = null;

    // Declare some local lambdas
    SimpleLambda simpleLambda = () -> { /*NOP*/ };

    ParameterLambda paramLambda =
      (int primitive, Object reference, DummyGeneric<Integer> specalisedGeneric) -> {};
    ArrayParameterLambda arrayParamLambda =
      (int[] primitive, Object[] reference, DummyGeneric<Integer>[] specalisedGeneric) -> {};

    ReturningLambdaPrimitive returnPrimitiveLambda = () -> {
      return 1;
    };
    ReturningLambdaReference returnReferenceLambda = () -> {
      return null;
    };
    ReturningLambdaSpecalisedGeneric returningSpecalisedGenericLambda = () -> {
      return null;
    };

    ReturningLambdaPrimitiveArray returnPrimitiveArrayLambda = () -> {
      return null;
    };
    ReturningLambdaReferenceArray returnReferenceArrayLambda = () -> {
      return null;
    };
    ReturningLambdaSpecalisedGenericArray returningSpecalisedGenericArrayLambda = () -> {
      return null;
    };

    ReturningLambdaPrimitive returnPrimitiveLambdaCapture = () -> {
      return localPrimitive;
    };
    ReturningLambdaReference returnReferenceLambdaCapture = () -> {
      return localReference;
    };
    ReturningLambdaSpecalisedGeneric returningSpecalisedGenericLambdaCapture = () -> {
      return localSpecalisedGeneric;
    };

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
