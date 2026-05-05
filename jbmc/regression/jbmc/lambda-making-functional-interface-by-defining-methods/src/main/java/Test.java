public class Test {

  interface TwoUndef {

    int f(int x);
    int g(int x);

  }

  interface OneUndefDirect extends TwoUndef {

    default int f(int x) { return x + 1; }

  }

  interface OneUndefIndirect extends OneUndefDirect, TwoUndef {

  }

  interface OneDef {

    default int h(int x) { return x + 1; }

  }

  interface MakeOneDefAbstract {

    int h(int x);

  }

  public static void main(String[] args) {

    OneUndefDirect test1 = x -> x + 2;
    OneUndefIndirect test2 = x -> x + 2;
    MakeOneDefAbstract test3 = x -> x + 2;
    assert test1.f(1) == 2;
    assert test1.g(1) == 3;
    assert test2.f(1) == 2;
    assert test2.g(1) == 3;
    assert test3.h(1) == 3;
    assert false; // Check we got here

  }

}
