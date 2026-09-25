// Per [temp.inst]/1: a class template specialization is implicitly
// instantiated when a completeness of the class type is required.
// Before the completeness is required, the specialization is not
// instantiated.

// Class template with a static counter (side-effect of definition).
template <class T>
struct has_value
{
  T value;
  static const int present = 1;
};

// A second template that does NOT touch the class type.
template <class T>
void use_pointer(T *)
{
  // only the type's name, not its completeness, is required here
}

int main()
{
  // Before any use requiring completeness, the declaration merely
  // names has_value<int>.  Passing a pointer does not require the
  // class to be complete.
  has_value<int> *p = 0;
  use_pointer(p);
  __CPROVER_assert(p == 0, "incomplete use kept p = 0");

  // Now request a member — this triggers instantiation.
  has_value<int> v;
  v.value = 42;
  __CPROVER_assert(v.value == 42, "member access after instantiation");
  __CPROVER_assert(
    has_value<int>::present == 1, "static member after instantiation");

  return 0;
}
