// An out-of-line definition of a member function template of a class
// template may name its parameters differently from the in-class
// declaration ([dcl.fct]/3: parameter names are not part of the function
// type).  libstdc++ does this, e.g. std::_Rb_tree declares
// `_M_insert_unique(_Arg&& __x)` but defines it with `_Arg&& __v`.
//
// CBMC built the instantiated member's signature from the declaration but
// took its body from the out-of-line definition, so the body referred to
// parameter names that did not exist in the instance.  Type-checking the
// body then failed and (for system-header bodies) the body was silently
// dropped, leaving the member function with no body — it returned a
// nondeterministic value.

template <class T>
struct Tree
{
  T storage;
  bool has = false;
  template <class U>
  bool put(U &&x); // declaration: parameter named `x`
};

template <class T>
template <class U>
bool Tree<T>::put(U &&u) // definition: parameter named `u` (differs)
{
  storage = u;
  has = true;
  return true;
}

int main()
{
  Tree<int> t;
  bool r = t.put(42);
  __CPROVER_assert(r, "out-of-line member template body is used");
  __CPROVER_assert(t.storage == 42, "member template body stored the value");
  __CPROVER_assert(t.has, "member template body ran its statements");
  return 0;
}
