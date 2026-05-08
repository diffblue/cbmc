public class Bar {
  private static int c = Util.setTo(10);
  private int x;

  public Bar(int x) {
    this.x = Util.setTo(x);
  }

  public int get() {
    return x + c;
  }
}
