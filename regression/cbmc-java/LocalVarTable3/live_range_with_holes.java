
public class live_range_with_holes {

  public static void main(int arg) {

    int x;
    int y;
    switch(arg) {
      case 1:
        x = 1;
        y = 1;
        break;
      case 2:
        x = 2;
        y = 2;
        break;
      default:
        x = 0;
        y = 0;
        break;
    }
    assert(x >= 0 && x <= 2);

  }

}
