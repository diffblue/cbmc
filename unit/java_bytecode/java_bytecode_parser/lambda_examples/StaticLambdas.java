public class StaticLambdas {

  static int staticPrimitive;
  static Object staticReference;
  static DummyGeneric<Integer> staticSpecalisedGeneric;

  static SimpleLambda simpleLambda = () -> { /*NOP*/ };
  static ParameterLambda paramLambda = (int primitive, Object reference, DummyGeneric<Integer> specalisedGeneric) -> {};
  static ArrayParameterLambda arrayParamLambda = (int[] primitive, Object[] reference, DummyGeneric<Integer>[] specalisedGeneric) -> {};
  static ReturningLambdaPrimitive returnPrimitiveLambda = () -> { return 1; };
  static ReturningLambdaReference returnReferenceLambda = () -> { return null; };
  static ReturningLambdaSpecalisedGeneric returningSpecalisedGenericLambda = () -> { return null; };
  static ReturningLambdaPrimitiveArray returnPrimitiveArrayLambda = () -> { return null; };
  static ReturningLambdaReferenceArray returnReferenceArrayLambda = () -> { return null; };
  static ReturningLambdaSpecalisedGenericArray returningSpecalisedGenericArrayLambda = () -> { return null; };

  static ReturningLambdaPrimitive returnPrimitiveLambdaCapture = () -> { return staticPrimitive; };
  static ReturningLambdaReference returnReferenceLambdaCapture = () -> { return staticReference; };
  static ReturningLambdaSpecalisedGeneric returningSpecalisedGenericLambdaCapture = () -> { return staticSpecalisedGeneric; };


  public static void testMethod() {
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
