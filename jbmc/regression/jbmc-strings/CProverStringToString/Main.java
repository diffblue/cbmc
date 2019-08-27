import org.cprover.CProverString;

class Main {
  public void testIntSuccess(int choice) {
    int i;
    String r;

    switch (choice) {
    case 0:
      i = 0;
      r = "0";
      break;
    case 1:
      i = 1;
      r = "1";
      break;
    case 2:
      i = -1;
      r = "-1";
      break;
    case 3:
      i = Integer.MIN_VALUE;
      r = "-2147483648";
      break;
    case 4:
      i = Integer.MAX_VALUE;
      r = "2147483647";
      break;
    default:
      return;
    }

    String s = CProverString.toString(i);
    assert s.equals(r);
  }

  public void testIntFailure() {
    String s = CProverString.toString(123);
    assert s.equals("0");
  }

  public void testIntWithRadixTwoSuccess(int choice) {
    int i;
    String r;

    switch (choice) {
    case 0:
      i = 0;
      r = "0";
      break;
    case 1:
      i = 1;
      r = "1";
      break;
    case 2:
      i = -1;
      r = "-1";
      break;
    case 3:
      i = 12;
      r = "1100";
      break;
    case 4:
      i = Integer.MIN_VALUE;
      r = "-10000000000000000000000000000000";
      break;
    case 5:
      i = Integer.MAX_VALUE;
      r = "1111111111111111111111111111111";
      break;
    default:
      return;
    }

    String s = CProverString.toString(i, 2);
    assert s.equals(r);
  }

  public void testIntWithRadixTwoFailure() {
    String s = CProverString.toString(123, 2);
    assert s.equals("0");
  }

  public void testIntWithRadixSixteenSuccess(int choice) {
    int i;
    String r;

    switch (choice) {
    case 0:
      i = 0;
      r = "0";
      break;
    case 1:
      i = 1;
      r = "1";
      break;
    case 2:
      i = -1;
      r = "-1";
      break;
    case 3:
      i = 56564;
      r = "dcf4";
      break;
    case 4:
      i = Integer.MIN_VALUE;
      r = "-80000000";
      break;
    case 5:
      i = Integer.MAX_VALUE;
      r = "7fffffff";
      break;
    default:
      return;
    }

    String s = CProverString.toString(i, 16);
    assert s.equals(r);
  }

  public void testIntWithRadixSixteenFailure() {
    String s = CProverString.toString(123, 16);
    assert s.equals("0");
  }

  public void testLongSuccess(int choice) {
    long l;
    String r;

    switch (choice) {
    case 0:
      l = 0;
      r = "0";
      break;
    case 1:
      l = 1;
      r = "1";
      break;
    case 2:
      l = -1;
      r = "-1";
      break;
    case 3:
      l = Long.MIN_VALUE;
      r = "-9223372036854775808";
      break;
    case 4:
      l = Long.MAX_VALUE;
      r = "9223372036854775807";
      break;
    default:
      return;
    }

    String s = CProverString.toString(l);
    assert s.equals(r);
  }

  public void testLongFailure() {
    String s = CProverString.toString(9223372036854775807L);
    assert s.equals("0");
  }

  public void testLongWithRadixTwoSuccess(int choice) {
    long l;
    String r;

    switch (choice) {
    case 0:
      l = 0;
      r = "0";
      break;
    case 1:
      l = 1;
      r = "1";
      break;
    case 2:
      l = -1;
      r = "-1";
      break;
    case 3:
      l = 12;
      r = "1100";
      break;
    case 4:
      l = Long.MIN_VALUE;
      r = "-1000000000000000000000000000000000000000000000000000000000000000";
      break;
    case 5:
      l = Long.MAX_VALUE;
      r = "111111111111111111111111111111111111111111111111111111111111111";
      break;
    default:
      return;
    }

    String s = CProverString.toString(l, 2);
    assert s.equals(r);
  }

  public void testLongWithRadixTwoFailure() {
    String s = CProverString.toString(9223372036854775807L, 2);
    assert s.equals("0");
  }

  public void testLongWithRadixSixteenSuccess(int choice) {
    long l;
    String r;

    switch (choice) {
    case 0:
      l = 0;
      r = "0";
      break;
    case 1:
      l = 1;
      r = "1";
      break;
    case 2:
      l = -1;
      r = "-1";
      break;
    case 3:
      l = 56564;
      r = "dcf4";
      break;
    case 4:
      l = Long.MIN_VALUE;
      r = "-8000000000000000";
      break;
    case 5:
      l = Long.MAX_VALUE;
      r = "7fffffffffffffff";
      break;
    default:
      return;
    }

    String s = CProverString.toString(l, 16);
    assert s.equals(r);
  }

  public void testLongWithRadixSixteenFailure() {
    String s = CProverString.toString(9223372036854775807L, 16);
    assert s.equals("0");
  }

  public void testFloatSuccess(int choice) {
    float f;
    String r;

    switch (choice) {
    case 0:
      f = 0F;
      r = "0.0";
      break;
    case 1:
      f = 1F;
      r = "1.0";
      break;
    case 2:
      f = -1F;
      r = "-1.0";
      break;
    case 3:
      f = 1.1F;
      r = "1.1";
      break;
    case 4:
      f = Float.MAX_VALUE;
      r = "3.4028235E38";
      break;
    case 5:
      f = Float.MIN_VALUE;
      r = "1.4E-45";
      break;
    case 6:
      f = Float.POSITIVE_INFINITY;
      r = "Infinity";
      break;
    case 7:
      f = Float.NEGATIVE_INFINITY;
      r = "-Infinity";
      break;
    case 8:
      f = Float.NaN;
      r = "NaN";
      break;
    default:
      return;
    }

    String s = CProverString.toString(f);
    assert s.equals(r);
  }

  public void testFloatFailure() {
    String s = CProverString.toString(1.1F);
    assert s.equals("0");
  }
}
