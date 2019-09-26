class My {

  byte byteField;
  short shortField;
  int intField;
  long longField;
  float floatField;
  double doubleField;

  static byte byteFieldStatic;
  static short shortFieldStatic;
  static int intFieldStatic;
  static long longFieldStatic;
  static float floatFieldStatic;
  static double doubleFieldStatic;

  int[] intArrField;

  public static void numericalArg(byte byteArg, short shortArg, int intArg,
   long longArg, float floatArg, double doubleArg) {
    if (byteArg > 3) {
      assert false;
    } else if (byteArg < 1) {
      assert false;
    } else if (byteArg < -1) {
      assert false;
    } else if (shortArg > 3) {
      assert false;
    } else if (shortArg < 1) {
      assert false;
    } else if (shortArg < -1) {
      assert false;
    } else if (intArg > 3) {
      assert false;
    } else if (intArg < 1) {
      assert false;
    } else if (intArg < -1) {
      assert false;
    } else if (longArg > 3) {
      assert false;
    } else if (longArg < 1) {
      assert false;
    } else if (longArg < -1) {
      assert false;
    } else if (floatArg > 3) {
      assert false;
    } else if (floatArg < 1) {
      assert false;
    } else if (floatArg < -1) {
      assert false;
    } else if (doubleArg > 3) {
      assert false;
    } else if (doubleArg < 1) {
      assert false;
    } else if (doubleArg < -1) {
      assert false;
    } else {
      assert false;
    }
  }

  public static void classArg(Other arg) {
    if (arg.byteField > 3) {
      assert false;
    } else if (arg.byteField < 1) {
      assert false;
    } else if (arg.shortField > 3) {
      assert false;
    } else if (arg.shortField < 1) {
      assert false;
    } else if (arg.intField > 3) {
      assert false;
    } else if (arg.intField < 1) {
      assert false;
    } else if (arg.longField > 3) {
      assert false;
    } else if (arg.longField < 1) {
      assert false;
    } else if (arg.floatField > 3) {
      assert false;
    } else if (arg.floatField < 1) {
      assert false;
    } else if (arg.doubleField > 3) {
      assert false;
    } else if (arg.doubleField < 1) {
      assert false;
    } else {
      assert false;
    }
  }

  public void field() {
    if (byteField > 3) {
      assert false;
    } else if (byteField < 1) {
      assert false;
    } else if (shortField > 3) {
      assert false;
    } else if (shortField < 1) {
      assert false;
    } else if (intField > 3) {
      assert false;
    } else if (intField < 1) {
      assert false;
    } else if (longField > 3) {
      assert false;
    } else if (longField < 1) {
      assert false;
    } else if (floatField > 3) {
      assert false;
    } else if (floatField < 1) {
      assert false;
    } else if (doubleField > 3) {
      assert false;
    } else if (doubleField < 1) {
      assert false;
    } else {
      assert false;
    }
  }

  public void fieldStatic() {
    if (byteFieldStatic > 3) {
      assert false;
    } else if (byteFieldStatic < 1) {
      assert false;
    } else if (shortFieldStatic > 3) {
      assert false;
    } else if (shortFieldStatic < 1) {
      assert false;
    } else if (intFieldStatic > 3) {
      assert false;
    } else if (intFieldStatic < 1) {
      assert false;
    } else if (longFieldStatic > 3) {
      assert false;
    } else if (longFieldStatic < 1) {
      assert false;
    } else if (floatFieldStatic > 3) {
      assert false;
    } else if (floatFieldStatic < 1) {
      assert false;
    } else if (doubleFieldStatic > 3) {
      assert false;
    } else if (doubleFieldStatic < 1) {
      assert false;
    } else {
      assert false;
    }
  }

  public static void fieldStaticNoClinit() {
    if (OtherNoClinit.intFieldStatic > 3) {
      assert false;
    } else if (OtherNoClinit.intFieldStatic < 1) {
      assert false;
    } else {
      assert false;
    }
  }

  public void classArrArg(Other other, int [] intArr) {
    if (other.intArrField.length > 3) {
      if (other.intArrField[2] > 3) {
        assert false;
      } else if (other.intArrField[2] < 1) {
        assert false;
      } else {
        assert false;
      }
    } else if (intArr.length > 3) {
      if (intArr[2] > 3) {
        assert false;
      } else if (intArr[2] < 1) {
        assert false;
      } else {
        assert false;
      }
    } else if (intArrField.length > 3) {
      if (intArrField[2] > 3) {
        assert false;
      } else if (intArrField[2] < 1) {
        assert false;
      } else {
        assert false;
      }
    } else {
      assert false;
    }
  }

  public static void intervalUnion(int intArg) {
    if (intArg == -3) {
      assert false;
    } else if (intArg == -1) {
      assert false;
    } else if (intArg == 0) {
      assert false;
    } else if (intArg == 1) {
      assert false;
    } else if (intArg == 3) {
      assert false;
    } else if (intArg == 6) {
      assert false;
    } else {
      assert false;
    }
  }
}
