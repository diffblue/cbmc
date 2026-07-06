// N5008 [class.mem]/[temp.inst]: a default member initializer (NSDMI) may refer
// to the enclosing class template's parameters.  When the template is
// instantiated, those parameter references -- including a non-type parameter
// used in an expression -- must be substituted with the corresponding template
// arguments.  Here `int tag = B ? 1 : 2;` and `int tag = B ? 7 : 9;` must see
// the instantiation's value of the non-type parameter `B`, both when `B` is
// given explicitly and when it is defaulted from a variable template.

extern "C" void __CPROVER_assert(int, const char *);

template <bool B>
struct holder
{
  int tag = B ? 1 : 2;
};

// A variable template feeding the defaulted non-type parameter, so the NSDMI
// substitution must survive default-argument evaluation as well.
template <typename T>
struct is_ptr
{
  static constexpr bool value = false;
};

template <typename T>
struct is_ptr<T *>
{
  static constexpr bool value = true;
};

template <typename T>
inline constexpr bool is_ptr_v = is_ptr<T>::value;

template <typename T, bool B = is_ptr_v<T>>
struct tagged
{
  int tag = B ? 7 : 9;
};

int main()
{
  // Local (function-body) instantiations: the implicit default constructor
  // runs each NSDMI, which must evaluate with the substituted parameter.
  holder<true> ht;
  holder<false> hf;
  tagged<int> ti;   // is_ptr_v<int>  == false -> tag 9
  tagged<int *> tp; // is_ptr_v<int*> == true  -> tag 7

  __CPROVER_assert(ht.tag == 1, "B=true -> 1");
  __CPROVER_assert(hf.tag == 2, "B=false -> 2");
  __CPROVER_assert(ti.tag == 9, "var-tmpl default false -> 9");
  __CPROVER_assert(tp.tag == 7, "var-tmpl default true -> 7");

  // Non-vacuity guard: a deliberately wrong property that must FAIL.  Before
  // the fix the specialization failed to type-check and the unsupported-
  // construct leniency swallowed it, yielding a vacuous VERIFICATION
  // SUCCESSFUL; this assertion keeps the test honest.
  __CPROVER_assert(ht.tag == 2, "WRONG: must fail");

  return 0;
}
