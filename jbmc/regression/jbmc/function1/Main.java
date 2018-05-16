
class Other
{
  public void fail()
  {
    assert i == 0;
  }

  private int i;
}

public class Main
{
  public static void main(String[] args)
  {
    Other o = new Other();
  }
}

