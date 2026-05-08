
public class live_range_exception {
  public static void main() {
    int x;
    int y;
    try
    {
      x = 0;
      y = 0;
    }
    catch(Exception e)
    {
      x = 1;
      y = 1;
    }
    assert(x==0 || x==1);
  }
}
