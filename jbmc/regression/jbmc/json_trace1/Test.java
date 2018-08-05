public class Test {

  byte main(byte[] a) {
    if (a.length != 9) {
      return -1;
    }

    byte diff = 0;
    for (byte i = 0; i < 9; i++) {
      if (a[i] == 1) {
        diff++;
      } else if (a[i] == 2) {
        diff--;
      } else if (a[i] != 0) {
        return -1;
      }
    }

    assert a[0] == 0;
    return -1;
  }
}
