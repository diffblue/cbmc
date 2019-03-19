public class Test {

  public static void main(int unknown) {

    try {
      mayThrow(unknown % 7 == 5);
    }
    catch(Exception e) {
    }

    // This test checks that symex can tell there is no exception in flight
    // (i.e. @inflight_exception is null) at this point, requiring it to
    // converge the `if @inflight_exception == null` test on mayThrow's return
    // with the explicit `@inflight_exception = null;` assignment that concludes
    // the catch block.

    // If it knows that, it will also know the following catch block is
    // unreachable; if not it will pursue both paths.
    try {
      mayThrow(false);
    }
    catch(Exception e) {
      unreachable();
    }

    // Try it once more, to check we also know after an unreachable catch that
    // there is still no inflight exception
    try {
      mayThrow(false);
    }
    catch(Exception e) {
      unreachable();
    }

  }

  public static void mayThrow(boolean shouldThrow) throws Exception {
    if(shouldThrow)
      throw new Exception();
  }

  public static void unreachable() { assert false; }

}
