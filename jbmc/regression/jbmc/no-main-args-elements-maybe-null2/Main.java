public class Main
{
  static void main(String[] args) // not public!
  {
    if(args != null && args.length>0) {
      assert(args[0] == null); // allowed to fail
    }
  }
}
