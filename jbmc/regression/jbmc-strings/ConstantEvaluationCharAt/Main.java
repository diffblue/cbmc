public class Main {
  public void constantCharAt() {
    StringBuilder sb = new StringBuilder("abc");
    char c = sb.charAt(1);
    assert c == 'b';
  }
}
