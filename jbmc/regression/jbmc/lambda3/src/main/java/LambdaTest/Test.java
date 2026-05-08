package LambdaTest;

interface Lamb1 {
  public Integer lambFunc1(Integer x);
}

class Test {

  public static Integer recvLambda(Integer y, Integer z) {
    Lamb1 lmb1 = (x) -> x = y + z; // Initializing in a lambda statement
    if (lmb1 != null && z != null) {
      return lmb1.lambFunc1(y);
    }
    return lmb1.lambFunc1(z);
  }
}
