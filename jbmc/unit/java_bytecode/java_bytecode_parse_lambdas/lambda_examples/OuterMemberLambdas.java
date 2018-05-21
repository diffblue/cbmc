public class OuterMemberLambdas {

  int memberPrimitive;
  Object memberReference;
  DummyGeneric<Integer> memberSpecalisedGeneric;

  public class Inner {

    ReturningLambdaPrimitive returnPrimitiveLambdaCapture = () -> { return memberPrimitive; };
    ReturningLambdaReference returnReferenceLambdaCapture = () -> { return memberReference; };
    ReturningLambdaSpecalisedGeneric returningSpecalisedGenericLambdaCapture = () -> { return memberSpecalisedGeneric; };


    public void testMethod() {

      returnPrimitiveLambdaCapture.Execute();
      returnReferenceLambdaCapture.Execute();
      returningSpecalisedGenericLambdaCapture.Execute();
    }
  }
}

