
import java.util.ArrayList;

public class Test9 extends Parent9 implements StaticInterface9 {

  public static int main() {
    return x;
  }

}

class Parent9 {
  private static int x; // should be invisible to Test9
}

interface StaticInterface9 {
  // The ArrayList is only here to define a constant x that
  // is complicated enough for javac to generate a static init
  // rather than just propagate the constant to all users.
  static ArrayList<Integer> al = new ArrayList<Integer>();
  static int x = al.size();
}
