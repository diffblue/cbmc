class My {

  String field;

  public static void stringArrayArg(String[] arg) {
    if (arg == null) {
      assert false;
    } else {
      assert false;
    }
  }

  public static void stringArg(String arg) {
    if (arg == null) {
      assert false;
    } else {
      assert false;
    }
  }

  public static void classArg(Other arg) {
    if (arg == null) {
      assert false;
    } else if (arg.stringField != null) {
      assert false;
    } else if (arg.otherField != null) {
      assert false;
    } else if (arg.other2Field != null) {
      assert false;
    }
  }

  public void field() {
    if (field == null) {
      assert false;
    } else {
      assert false;
    }
  }

}
