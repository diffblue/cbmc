
public class Test {

  public static void main() {

    String s = Opaque.getstr();
    if(s != null)
      assert s.length() <= 10;

  }

}
