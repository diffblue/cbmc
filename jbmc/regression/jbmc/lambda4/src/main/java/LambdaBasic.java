public class LambdaBasic {

  private boolean endOnSuccess = true;

  public void testThis(int branch) {
    boolean endOnSuccess;
    endOnSuccess = this.endOnSuccess;
    If boo = () -> {
      if (endOnSuccess) {
        return 1;
      }
      return 0;
    };

    int x0 = boo.xInt();
    // assert successful
    if (branch == 1) {
      if (endOnSuccess) {
        assert x0 == 1;
      } else {
        assert x0 == 0;
      }
      // assert failed
    } else {
      if (endOnSuccess) {
        assert x0 != 1;
      } else {
        assert x0 != 0;
      }
    }
  }

  interface If {

    int xInt();
  }
}
