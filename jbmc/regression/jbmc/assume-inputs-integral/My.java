class My {

  float floatField;
  double doubleField;

  static float floatFieldStatic;
  static double doubleFieldStatic;

  double[] doubleArrField;

  public static void numericalArg(float floatArg, double doubleArg) {
    if (floatArg == 1.08f) {
      assert false;
    } else if (floatArg == Float.POSITIVE_INFINITY) {
      assert false;
    } else if (floatArg == Float.NEGATIVE_INFINITY) {
      assert false;
    } else if (floatArg == Float.NaN) {
      assert false;
    } else if (doubleArg == 1.08) {
      assert false;
    } else if (doubleArg == Double.POSITIVE_INFINITY) {
      assert false;
    } else if (doubleArg == Double.NEGATIVE_INFINITY) {
      assert false;
    } else if (doubleArg == Double.NaN) {
      assert false;
    } else if (doubleArg != floatArg) {
      assert false;
    } else {
      assert false;
    }
  }

  public static void classArg(Other arg) {
    if (arg.floatField == 1.08f) {
      assert false;
    } else if (arg.floatField == Float.POSITIVE_INFINITY) {
      assert false;
    } else if (arg.floatField == Float.NEGATIVE_INFINITY) {
      assert false;
    } else if (arg.floatField == Float.NaN) {
      assert false;
    } else if (arg.doubleField == 1.08) {
      assert false;
    } else if (arg.doubleField == Double.POSITIVE_INFINITY) {
      assert false;
    } else if (arg.doubleField == Double.NEGATIVE_INFINITY) {
      assert false;
    } else if (arg.doubleField == Double.NaN) {
      assert false;
    } else {
      assert false;
    }
  }

  public void field() {
    if (floatField == 1.08f) {
      assert false;
    } else if (floatField == Float.POSITIVE_INFINITY) {
      assert false;
    } else if (floatField == Float.NEGATIVE_INFINITY) {
      assert false;
    } else if (floatField == Float.NaN) {
      assert false;
    } else if (doubleField == 1.08) {
      assert false;
    } else if (doubleField == Double.POSITIVE_INFINITY) {
      assert false;
    } else if (doubleField == Double.NEGATIVE_INFINITY) {
      assert false;
    } else if (doubleField == Double.NaN) {
      assert false;
    } else {
      assert false;
    }
  }

  public void fieldStatic() {
    if (floatFieldStatic == 1.08f) {
      assert false;
    } else if (floatFieldStatic == Float.POSITIVE_INFINITY) {
      assert false;
    } else if (floatFieldStatic == Float.NEGATIVE_INFINITY) {
      assert false;
    } else if (floatFieldStatic == Float.NaN) {
      assert false;
    } else if (doubleFieldStatic == 1.08) {
      assert false;
    } else if (doubleFieldStatic == Double.POSITIVE_INFINITY) {
      assert false;
    } else if (doubleFieldStatic == Double.NEGATIVE_INFINITY) {
      assert false;
    } else if (doubleFieldStatic == Double.NaN) {
      assert false;
    } else {
      assert false;
    }
  }

  public static void fieldStaticNoClinit() {
    if (OtherNoClinit.doubleFieldStatic == 1.08) {
      assert false;
    } else if (OtherNoClinit.doubleFieldStatic == Double.POSITIVE_INFINITY) {
      assert false;
    } else if (OtherNoClinit.doubleFieldStatic == Double.NEGATIVE_INFINITY) {
      assert false;
    } else if (OtherNoClinit.doubleFieldStatic == Double.NaN) {
      assert false;
    } else {
      assert false;
    }
  }

  public void arrayArg(Other other, double [] doubleArr) {
    if (other.doubleArrField.length > 3) {
      if (other.doubleArrField[2] == 1.08) {
        assert false;
      } else if (other.doubleArrField[2] == Double.POSITIVE_INFINITY) {
        assert false;
      } else if (other.doubleArrField[2] == Double.NEGATIVE_INFINITY) {
        assert false;
      } else if (other.doubleArrField[2] == Double.NaN) {
        assert false;
      } else {
        assert false;
      }
    } else if (doubleArr.length > 3) {
      if (doubleArr[2] == 1.08) {
        assert false;
      } else if (doubleArr[2] == Double.POSITIVE_INFINITY) {
        assert false;
      } else if (doubleArr[2] == Double.NEGATIVE_INFINITY) {
        assert false;
      } else if (doubleArr[2] == Double.NaN) {
        assert false;
      } else {
        assert false;
      }
    } else if (doubleArrField.length > 3) {
      if (doubleArrField[2] == 1.08) {
        assert false;
      } else if (doubleArrField[2] == Double.POSITIVE_INFINITY) {
        assert false;
      } else if (doubleArrField[2] == Double.NEGATIVE_INFINITY) {
        assert false;
      } else if (doubleArrField[2] == Double.NaN) {
        assert false;
      } else {
        assert false;
      }
    } else {
      assert false;
    }
  }
}
