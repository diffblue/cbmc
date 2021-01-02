public class SignalUtil {
  public static long abs1(int signal) {
    long result;
    if(signal >= 0)
      result = signal;
    else
      result = -1*signal;
    return result;
  }
  public static long abs2(int signal) {
    if(signal < 0)
      return -signal;
    else
      return signal;
  }
}
