public class generics {

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
}
