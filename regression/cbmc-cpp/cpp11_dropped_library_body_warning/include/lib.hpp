// stands in for a library header: bodies from `/include/` paths whose
// type-checking fails are dropped instead of failing the translation
#pragma once
inline int good_fn(int x)
{
  return x + 1;
}
inline int bad_fn(int x)
{
  typedef int v4 __attribute__((vector_size(16)));
  v4 a = {x, x, x, x};
  v4 b = __builtin_shuffle(a, (v4){3, 2, 1, 0}); // not modelled by CBMC
  return b[0];
}
