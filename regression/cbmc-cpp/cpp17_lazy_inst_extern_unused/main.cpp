// CORE guard for N5008 [temp.inst]/11 + [temp.explicit]: an explicit
// instantiation declaration (extern template) must NOT force instantiation of
// an unused, ill-formed-when-instantiated non-virtual member.  This exercises
// the explicit-instantiation / completion path that the inline member-body
// fix touches, ensuring it stays lazy for unused members.

template <class T>
struct S
{
  T value;
  void good() { value = value; }
  void bad() { T t; t.no_such_method(); } // ill-formed for T=int; never called
};

extern template struct S<int>;

int main()
{
  S<int> s;
  s.value = 3;
  s.good();
  __CPROVER_assert(s.value == 3, "value preserved");
  return 0;
}
