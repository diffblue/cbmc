public class generics {

  interface dummyInterface
  {
    int getX();
  }

  class element<E> {
    E elem;
  }

  class bound_element<NUM extends java.lang.Number> {
    NUM elem;
    NUM f() {
      return elem;
    }
    void g(NUM e) {
      elem=e;
    }
  }

  class double_bound_element<T extends java.lang.Number & dummyInterface>
  {
    T elem;
  }

// definitely need to do some tests with bounded two elements
  // the java_generic_type_from_string does not work for complex types
  // Need to to unblock just get it so it throws when failing rather than wrong
  class two_elements<K, V>
  {
    K k;
    V v;
  }



  public static boolean foo(String s)
  {
    if(s.length == 0)
      return true;
    return false;
  }

  bound_element<Integer> belem;

  Integer f(int n) {

    element<Integer> e=new element<>();
    e.elem=n;
    bound_element<Integer> be=new bound_element<>();
    belem=new bound_element<>();
    be.elem=new Integer(n+1);
    if(n>0)
      return e.elem;
    else
      return be.elem;
  }
}
