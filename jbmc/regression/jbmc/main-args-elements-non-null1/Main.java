public class Main
{
  public static void main(String[] args)
  {
    if(args.length>1)
    {
      assert(args[0] != null); // must hold
      assert(args[1] != null); // must hold
    }
  }
}
