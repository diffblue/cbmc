public class Main
{
  public static void main(String[] args)
  {
    assert args!=null; // should pass
    assert args.length==0; // should fail
    
    // check some setup
    assert args instanceof Object[];
  }
}

