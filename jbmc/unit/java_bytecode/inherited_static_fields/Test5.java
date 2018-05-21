
import java.util.ArrayList;

public class Test5 extends OpaqueParent5 implements OpaqueInterface5 {

  public static int main() {
    return x;
  }

}

class OpaqueParent5 {

}

interface OpaqueInterface5 {
  // The ArrayList is only here to define a constant x that
  // is complicated enough for javac to generate a static init
  // rather than just propagate the constant to all users.
  static ArrayList<Integer> al = new ArrayList<Integer>();
  static int x = al.size();
}
