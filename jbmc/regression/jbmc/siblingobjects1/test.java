
public class test {

  public Other o1;
  public Other o2;

  public void main() {
    if(o1 == null || o2 == null)
      return;
    assert(false);
  }

}

class Other {
  int x;
}
