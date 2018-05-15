
public class Test8 extends Parent8 {

  public static int main() {
    return x;
  }

}

class Parent8 {
  static int x; // package visibility, should be visible to Test8
}
