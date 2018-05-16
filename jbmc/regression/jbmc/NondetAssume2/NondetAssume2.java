import org.cprover.CProver;

class A { int x; }

class B { A a; }

class C { B b; }

class NondetAssume2
{
  void main()
  {
    C c = CProver.nondetWithNull();
    CProver.assume(c != null);
    assert c != null;
  }
}
