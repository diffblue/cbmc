extern "C" void __CPROVER_assert(bool, const char *);
enum class kind
{
  a,
  b,
  // [dcl.enum]/5: before the closing brace, an enumerator has the
  // underlying type
  c = b
};
int classify(kind k)
{
  // [stmt.switch]/2: a scoped enumeration condition is not promoted; the
  // case labels have its type
  switch(k)
  {
  case kind::a:
    return 1;
  case kind::b:
    return 2;
  }
  return 0;
}
int main()
{
  __CPROVER_assert(
    classify(kind::a) == 1 && classify(kind::c) == 2, "switch on enumeration");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
