
public class HasGeneric {

  public Generic<String> s;
  public Generic<Integer> t;
  public OtherGeneric<String> u;

}

class Generic<T> {
  T t;
}

class OtherGeneric<T> {
  Generic<T> gen;
}
