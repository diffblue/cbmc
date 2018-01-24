public class Main
{
  public static void main(int[] args)
  {
    assert(args == null); // allowed to fail
    assert(args != null); // allowed to fail
    if(args != null && args.length > 0) {
      try {
        int i = args[0];
      }
      catch(Exception e) {
        assert false; // must hold
      }
    }
  }
}
