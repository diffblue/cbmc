public class VarLengthArrayTrace1 {

  public static void main(int unknown, int arg2) {

    Container c = new Container(unknown);
    if(c.val != 2) return;
    int[] arr = new int[c.val];
    arr[1] = arg2;
    int test = arr[1];
    assert(test != 10);

  }

}

class Container {

  public Container(int v) { val = v; }
  int val;

}
