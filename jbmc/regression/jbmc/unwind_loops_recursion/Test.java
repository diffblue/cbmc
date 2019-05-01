public class Test {

  public static void recurse_down_from(int x) {
    if(x > 0)
      recurse_down_from(x - 1);
  }

  public static void main(String[] args) {
    for(int i = 0; i < 10; ++i) {
      if(i == args.length)
        break;
    }
    recurse_down_from(10);
  }

}
