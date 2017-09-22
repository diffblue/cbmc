public class Sync {
  public static void main(String[] args) {
    final Object o = null;
    try {
      synchronized (o) {}
      assert false;
    } catch (NullPointerException e) {
      return;
    }
  }
}
