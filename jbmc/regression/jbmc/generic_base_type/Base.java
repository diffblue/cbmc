
public class Base<T> { }

class Test<T> extends Base<T> {

  public void main(boolean unknown) {

    if(unknown)
      callee(getSpecialisedTest());
    else
      callee2(getUnspecialisedTest());

  }

  public Test<String> getSpecialisedTest() { return new Test<String>(); }
  public Test<T> getUnspecialisedTest() { return new Test<T>(); }

  public void callee(Base<String> b) { assert false; }
  public void callee2(Base<T> b) { assert false; }

}
