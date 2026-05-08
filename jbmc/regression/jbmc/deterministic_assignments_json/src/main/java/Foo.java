public class Foo {
  private int i;
  private Bar b;

  public Foo(int i, int x)
  {
    this.i = Util.setTo(i);
    this.b = new Bar(x);
  }

  public int get() {
    return i + b.get();
  }
}
