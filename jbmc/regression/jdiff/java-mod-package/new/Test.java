package com.diffblue.foo;

public class Test {

  public int foo(int x) {
    if (x > 10) {
      return x;
    } else {
      return x * 10;
    }
  }

  public int bar(int x) {
    if (x < 10) {
      return x;
    } else {
      return x / 10;
    }
  }
}
