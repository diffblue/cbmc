class ifxx1
{
  public static void main(String[] args)
  {
    int i = 0;
    if (i != 0) {
      assert false;
    }
    i = 1;
    if (i == 0) {
      assert false;
    }
    if (i < 0) {
      assert false;
    }
    i = 0;
    if (i > 0) {
      assert false;
    }
    i = 1;
    if (i <= 0) {
      assert false;
    }
    i = -1;
    if (i >= 0) {
      assert false;
    }
  }
}
