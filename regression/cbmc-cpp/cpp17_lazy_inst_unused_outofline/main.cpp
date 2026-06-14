// CORE guard for N5008 [temp.inst]/11: same as cpp17_lazy_inst_unused_inline
// but with an OUT-OF-LINE member definition.  The unused, ill-formed-when-
// instantiated bad() must not be instantiated and must not cause an error.

template <class T>
struct S
{
  T value;
  void good() { value = value; }
  void bad();
};

template <class T>
void S<T>::bad()
{
  T t;
  t.no_such_method(); // ill-formed for T=int; never called
}

int main()
{
  S<int> s;
  s.value = 7;
  s.good();
  __CPROVER_assert(s.value == 7, "value preserved");
  return 0;
}
