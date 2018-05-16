
class Other
{
  public void fail()
  {
    assert i == 0;
  }

  private int i;
}

class Other2 extends Other
{
  private int j;
}

public class Main
{
  public static void main(String[] args)
  {
    Other o = new Other();
  }
}

