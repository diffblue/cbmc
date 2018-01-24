public class Main
{
  public static void main(Main[] args)
  {
    if(args != null && args.length > 0) {
      assert(args[0] == null); // allowed to fail
    }
  }
}
