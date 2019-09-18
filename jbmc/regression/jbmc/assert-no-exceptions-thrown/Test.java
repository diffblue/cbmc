class MyException extends Exception {}

public class Test {
  public static int mayThrow(char branch) throws Throwable {
    if (branch == 'n') {
      throw new NullPointerException();
    } else if (branch == 'c') {
      throw new MyException();
    } else if (branch == 't') {
      throw new Throwable();
    } else if (branch == 'r') {
      return 2;
    } else {
      return 1;
    }
  }

  public static void check(char branch) {
    try {
      int i = mayThrow(branch);
      if (i == 2)
        assert false;
      if (i == 1)
        assert false;
    } catch (MyException e) {
      assert false;
    } catch (NullPointerException e) {
      assert false;
    } catch (Throwable e) {
      assert false;
    }
  }
}
