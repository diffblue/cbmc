
public class test {
 public static void main () {
   try {
     A a = null;
     a.f();
   }
   catch(NullPointerException e) {
     assert false;
   }
 }
}

class A {

  public void f() {}

}
