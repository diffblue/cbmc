package java.lang;

public class String {

  interface FunctionalIf {
    public int f(int x);
  }

  public static int usesLambdas(int x) {
    FunctionalIf lambda = (n -> n + 1);
    return lambda.f(x);
  }

}
