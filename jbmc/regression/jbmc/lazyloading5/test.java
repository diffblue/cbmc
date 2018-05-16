
public class test {

  public static void main() {

    assert(other.getx()==1);

  }

}

class other {

  public static int x;
  public static int getx() { return x; }

  static {
    x=1;
  }

}
