class if_icmp1
{
  private static void f() {
    int i = 10;
    int j = 11;
    if (i == j) {
      assert false;
    }
    if (i >= j) {
      assert false;
    }
    if (j > i) {
      assert true;
    } else {
      assert false;
    }
    if (j <= i) {
      assert false;
    }
    if (j < i) {
      assert false;
    } else {
      assert true;
    }
  }

  public static void main(String[] args)
  {
    f();
  }
}
