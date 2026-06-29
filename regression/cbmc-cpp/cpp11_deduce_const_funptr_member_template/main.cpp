// KNOWNBUG (front-end): deducing a function template parameter from a
// const-qualified function-pointer argument fails when the argument's type is
// a substituted class-template parameter.
//
// N5008 [temp.deduct.call]/3: for a forwarding reference `Fn&&` and an lvalue
// argument of type `const FP` (a const function pointer), `Fn` is deduced as
// `const FP&`; the deduced parameter is therefore `const FP&` and a const
// function-pointer lvalue binds it.  CBMC drops the `const` while building the
// deduced reference parameter (it becomes `FP&`), so the const argument no
// longer binds, the only (template) candidate is discarded during overload
// resolution, and -- because this happens inside the elaboration of an
// instantiated member's body -- the resolution silently fails and the whole
// body (`Mgr<FP>::clone`) is left with no body ("no body for callee").
//
// This is exactly the shape of libstdc++ std::function's
// `_Function_base::_Base_manager<F>::_M_manager` __clone_functor case, which
// calls `_M_init_functor(__dest, *const_cast<const _Functor*>(...))` with
// `_Functor` a function pointer; the silently-discarded body is why a single
// `std::function<int(int)> f = &fn;` reports `_M_manager` as no-body.
//
// When the front end preserves the const through the deduced reference,
// `run` executes and `sink` becomes g(41)==42.

extern "C" void __CPROVER_assert(int, const char *);

typedef int (*FP)(int);

int g(int x)
{
  return x + 1;
}

int sink;

template <class F>
struct Mgr
{
  // Forwarding-reference parameter; Fn is deduced from the argument.
  template <class Fn>
  static void run(Fn &&f)
  {
    sink = f(41);
  }

  static F getval()
  {
    return g;
  }

  static void clone()
  {
    const F cf = getval();
    // The argument is a `const F` lvalue (F == FP, a function pointer).
    // [temp.deduct.call]/3: Fn deduces to `const F&`.
    run(*const_cast<const F *>(&cf));
  }
};

int main()
{
  Mgr<FP>::clone();
  __CPROVER_assert(sink == 42, "member-template deduction from const funptr arg");
  __CPROVER_assert(sink == 0, "WRONG must FAIL");
  return 0;
}
