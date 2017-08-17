public class Test {
  public static void main(long[] a) {
    if(a.length<3)
      return;
    for(int i=0; i<a.length; i++) {
      a[i]=(long)i;
    }
  }
}
