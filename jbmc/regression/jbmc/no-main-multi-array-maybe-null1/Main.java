public class Main
{
  public static void main(String[][] args)
  {
     assert(args == null ||
     args.length == 0 ||
     args[0] == null ||
     args[0].length == 0 ||
     args[0][0] != null); // allowed to fail
  }
}
