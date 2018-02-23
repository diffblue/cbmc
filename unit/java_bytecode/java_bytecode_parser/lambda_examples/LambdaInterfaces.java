interface SimpleLambda {
  public void Execute();
}

interface ParameterLambda {
  public void Execute(int primitive, Object reference, DummyGeneric<Integer> specalisedGeneric);
}

interface ArrayParameterLambda {
  public void Execute(int[] primitive, Object[] reference, DummyGeneric<Integer>[] specalisedGeneric);
}

interface ReturningLambdaPrimitive {
  public int Execute();
}

interface ReturningLambdaReference {
  public Object Execute();
}

interface ReturningLambdaSpecalisedGeneric {
  public DummyGeneric<Integer> Execute();
}

interface ReturningLambdaPrimitiveArray {
  public int[] Execute();
}

interface ReturningLambdaReferenceArray {
  public Object[] Execute();
}

interface ReturningLambdaSpecalisedGenericArray {
  public DummyGeneric<Integer>[] Execute();
}

class DummyGeneric<T> {
  T field;
}
