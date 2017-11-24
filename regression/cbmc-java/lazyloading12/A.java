public class A
{
  public void me()
  {
    assert(G.x == 100);
  }

  public void me2()
  {
    G g = new G();
    assert(G.x == 100);
  }

  public void me3()
  {
    assert(J.x2 == 10);
  }
}

class G
{
  static int x = 100;
}

class J extends G
{
  static int x2;
  static {
    if(G.x == 100)
      x2=10;
    else
      x2=0;
    }
}
