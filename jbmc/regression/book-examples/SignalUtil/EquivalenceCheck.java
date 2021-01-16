public class EquivalenceCheck {
  public void check(int signal) {
    assert(SignalUtil.abs1(signal) == SignalUtil.abs2(signal));
  }
}
