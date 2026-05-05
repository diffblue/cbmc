class Problem {
  private static final Object[] DEFAULT = {};
  private Object data;

  Problem() {
    this.data = DEFAULT;
  }

  void checkInvariant() {
    assert data != null;
  }
}

public class Main {
  public static void main(String[] args) {
    new Problem().checkInvariant();
  }
}
