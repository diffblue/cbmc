class B
{
  void foo()
  {
  }
}

class A
{
  B b = new B();
}

public class Test
{
  // org.cprover.CProver.nondetWithoutNull(T) returns a nondeterministic
  // non-null object of the argument's type. After replace_java_nondet turns
  // it into a nondet side effect, convert_nondet's object factory materialises
  // it -- introducing `new` for A and its field B -- which remove_java_new
  // then lowers to an `allocate`.
  public A f00(A x)
  {
    return org.cprover.CProver.nondetWithoutNull(x);
  }
}
