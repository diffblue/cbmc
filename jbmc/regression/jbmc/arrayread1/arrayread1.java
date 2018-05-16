public class arrayread1 {

  static arrayread1 readback;

  public static void main(int c) {

    if(c!=1) return;
    arrayread1[] a = new arrayread1[c];
    readback=a[0];
    assert(readback==null);

  }

}
