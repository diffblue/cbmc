/**
 * Utility methods for tests related to retrieving (deterministic) initial
 * values of static fields from a JSON file.
 * These methods are generally used to initialize static fields using a loop, so
 * without the --static-values option, JBMC would need a very high unwind limit.
 * With the initial values given in a JSON file, lower unwind values can be
 * used.
 */
public class Util {

  public static int fib(int num) {
    int zeroFib = 0;
    int oneFib = 1;
    for (int i = 0; i < num; i++) {
      int temp = oneFib;
      oneFib = temp + zeroFib;
      zeroFib = temp;
    }
    return zeroFib;
  }

  public static int setTo(int value) {
    int sign = value >= 0 ? 1 : -1;
    int i = 0;
    for (; i < sign * value; i++) {
    }
    return sign * i;
  }

  public static String repeat(String part, int copies) {
    StringBuilder builder = new StringBuilder();
    for (int i = 0; i < copies; i++) {
      builder.append(part);
    }
    return builder.toString();
  }

}
