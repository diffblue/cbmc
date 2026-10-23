// stands in for a library header: bodies from `/include/` paths whose
// type-checking fails are dropped instead of failing the translation
#pragma once
inline int good_fn(int x)
{
  return x + 1;
}
inline int bad_fn(int x)
{
  // ill-formed on purpose ([expr.ref]/2: the object expression of `.' must
  // have class type): every compiler rejects this body, and the front end
  // must drop it with a diagnostic rather than fail the translation
  return x.value;
}
