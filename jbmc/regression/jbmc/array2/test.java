public class test {

  public void f(int unknown) {

    int[] arr;
    if(unknown > 0)
      arr = new int[1];
    else
      arr = new int[0];

    if(unknown > 0)
      arr[0]=1;

    if(unknown > 0)
      assert arr[0] == 1;
    else
      assert arr.length == 0;
  }

}
