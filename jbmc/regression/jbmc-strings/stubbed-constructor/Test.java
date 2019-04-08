import java.lang.String;

public class Test {

  public static void test() {
    char[] c1 = new char[] { 'j', 'a', 'v', 'a' };
    String s = new String (c1);
    assert s.charAt(0) == 'j';
  }

}
