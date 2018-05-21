class iarith2
{
  private static int i() {
    int value = 3;
    value &= 1;
    value |= 4;
    value ^= 4;
    value <<= 2;
    value >>= 1;
    value = -value;
    value >>>= 1;
    return value;
  }

  private static long l() {
    long value = 3L;
    value &= 1L;
    value |= 4L;
    value ^= 4L;
    value <<= 2L;
    value >>= 1L;
    value = -value;
    value >>>= 1L;
    return value;
  }

  private static void s() {
    short lhs = 127;
    short rhs = 32767;
    if (lhs < rhs) {
      return;
    }
    assert false;
  }

  public static void main(String[] args) {
    assert i() == 2147483647;
    assert l() == 9223372036854775807L;
    s();
  }
}
