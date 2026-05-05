package org.cprover;

public class MyClass {
  private int x;

  public MyClass(int x) {
    this.x = x;
  }

  public static class Inner {
    public static int doIt(int x) {
      return x;
    }
  }

  public int get() {
    return x;
  }
}
