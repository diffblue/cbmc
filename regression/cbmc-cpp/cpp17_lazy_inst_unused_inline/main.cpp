// CORE guard for N5008 [temp.inst]/8 + /11: an unused, non-virtual member
// function whose body would be ill-formed for this specialization must NOT
// cause an error, because [temp.inst]/11 forbids instantiating it ("shall not
// implicitly instantiate ... a non-virtual member function ... unless such
// instantiation is required").  bad() below is never odr-used.
//
// This guards the lazy-instantiation property while Option B (on-odr-use
// member instantiation) is implemented: if a step ever starts eagerly and
// hard-instantiating unused members, this test fails.

template <class T>
struct S
{
  T value;
  void good() { value = value; }
  void bad() { T t; t.no_such_method(); } // ill-formed for T=int; never called
};

int main()
{
  S<int> s;
  s.value = 5;
  s.good();
  __CPROVER_assert(s.value == 5, "value preserved");
  return 0;
}
