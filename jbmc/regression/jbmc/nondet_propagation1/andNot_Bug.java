public class andNot_Bug {
  public static void main(int capacity) {
    if(capacity < 1)
      return;
    boolean b1 = true;
    boolean b2[] = new boolean[capacity];
    b2[0] = false;

    for (int i = 0; i < b2.length; i++) {
      b1 = b1 && !b2[i];
    }
  }
}
