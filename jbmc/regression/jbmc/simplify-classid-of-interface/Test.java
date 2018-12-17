
public class Test {

  public static void main() {

    // The following line is only needed so that multiple possible callees
    // for the interface Intf are found, and so a dispatch table
    // (if i->@class_identfier == "Impl1" then ...) is generated.
    Impl2 unused = new Impl2();

    // This should be easily verified, as long as symex can determine that *i
    // certainly refers to an instance of Impl1, and so i.f() is certainly a
    // call to Impl1.f. This requires it to simplify the expression
    // "((struct Intf)some_impl1_instance).@java.lang.Object.@class_identifier".
    Intf i = new Impl1();
    int got = i.f();
    assert got == 1;

  }

  public static void main_derived_class() {

    // This is just like the "main" method, except a class with a superclass
    // is used, to check that the cast to struct Intf can be simplified even
    // when the object doesn't directly have such a member (instead it has a
    // member "@Impl1", which itself has a "@java.lang.Object").

    Impl2 unused = new Impl2();

    Intf i = new Impl1Sub();
    int got = i.f();
    assert got == 1;

  }

}

class Impl1 implements Intf {

  // This field is important-- without it, the structures of Impl1 and Intf
  // are the same (both being simply { java.lang.Object @java.lang.Object }),
  // which allows the expression simplifier to take an easier route than the one
  // we intend to test.
  public int x;

  public int f() {
    return 1;
  }

}

class Impl1Sub extends Impl1 {

  public int z;

}

class Impl2 implements Intf {

  public int f() {
    return 2;
  }

}
