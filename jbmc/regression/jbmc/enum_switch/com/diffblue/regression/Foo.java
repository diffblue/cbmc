package com.diffblue.regression;

public class Foo {
  public int foo(MyEnum e) {
    if (e == null) return 0;
    switch (e) {
      case A:
        assert false;
        return 1;
      case B:
        assert false;
        return 2;
      case C:
        assert false;
        return 3;
    }
    assert false;
    return 5;
  }
}
