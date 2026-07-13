// N5008 [temp.variadic]/5 + [dcl.init.aggr]: a variadic function template whose
// body expands a pack of CALLS inside a BRACED (aggregate) initializer:
//   template <class... E> box mk(E&&... e) { return box{fwd(e)...}; }
//
// CORE (was KNOWNBUG): the instantiate-time body pack expander replicated a
// pack expansion inside a function-CALL argument list but not inside a braced /
// aggregate initializer, so `fwd(e)...` was mis-expanded to a single
// `fwd(e$0, e$1)` (retaining the `...`); the malformed body failed to convert
// and was dropped ("no body for callee").  Fixed by expanding an
// ID_initializer_list's pack-expansion elements like function-call arguments.
//
// g++ compiles and runs {10, 20, 30}; clang++ accepts.  Non-vacuous: the result
// is a concrete function of the forwarded arguments.

extern "C" void __CPROVER_assert(int, const char *);

struct box2
{
  int a, b;
};

struct box3
{
  int a, b, c;
};

template <class T>
T &&fwd(T &x)
{
  return static_cast<T &&>(x);
}

template <class... E>
box2 mk2(E &&... e)
{
  return box2{fwd(e)...};
}

template <class... E>
box3 mk3(E &&... e)
{
  return box3{fwd(e)...};
}

int main()
{
  auto b = mk2(10, 20);
  __CPROVER_assert(b.a == 10 && b.b == 20, "arity 2: {10,20}");
  auto c = mk3(10, 20, 30);
  __CPROVER_assert(
    c.a == 10 && c.b == 20 && c.c == 30, "arity 3: {10,20,30}");
  return 0;
}
