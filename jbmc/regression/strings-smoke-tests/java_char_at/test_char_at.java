public class test_char_at {

  public static void main() {
    String s = new String("abc");
    assert(org.cprover.CProverString.charAt(s, 2)=='c');
  }
}
