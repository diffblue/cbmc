
public class Base<T> {

  public T genericData;
  public String nonGenericData;

  public void main(boolean unknown1, boolean unknown2) {

    Base b = unknown1 ? new Impl1<T>() : new Impl2<T>();
    if(unknown2)
      b.f(genericData);
    else
      b.g(nonGenericData);
  }

  public void f(T t) { }
  public void g(String t) { }

}

class Impl1<T> extends Base<T> {

  public void f(T t) { assert false; }
  public void g(String t) { assert false; }

}

class Impl2<T> extends Base<T> {

  public void f(T t) { assert false; }
  public void g(String t) { assert false; }

}
