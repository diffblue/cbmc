public class generics {

  class GList<V> {
  }

  class GMap<K,V> {
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

  class double_element<A,B> {
    A first;
    B second;
    GMap<A,B> map;

    void insert(A a, B b) {
      first=a;
      second=b;
    }

    void setMap(GMap<A,B> m) {
      map=m;
    }
  }

  class compound_element<B> {
    GList<B> elem;

    void setFixedElem(GList<Integer> e) {
      elem=null;
    }

    GList<B> getElem() {
      return elem;
    }
  }
}
