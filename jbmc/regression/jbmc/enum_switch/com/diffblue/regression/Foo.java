package com.diffblue.regression;

public class Foo {
  public int foo(MyEnum e) {
    if (e == null) return 0;
    switch (e) {
      case A:
        return 1;
      case B:
        return 2;
      case C:
        return 3;
    }
    return 5;
  }
}
