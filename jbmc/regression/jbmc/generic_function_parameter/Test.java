
public class Test<T> {

  public void main(Test<String> param) {

    callee(param);

  }

  public void callee(Test<String> param) {

    assert false;

  }

  public void main2(Test<String> param) {

    callee2((Test<T>)param);

  }

  public void callee2(Test<T> param) {

    assert false;

  }

}
