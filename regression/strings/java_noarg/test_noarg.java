public class test_noarg {

  public static void main(/* NO ARGUMENT*/) {
    String s = new String("Hello World!");
    char c = s.charAt(4);
    StringBuilder sb = new StringBuilder(s);
    sb.setCharAt(5,'-');
    s = sb.toString();
    assert(c == 'o');
    assert(c == 'p');
    assert(s.equals("Hello-World!"));
  }
}
