extern "C" void __CPROVER_assert(bool, const char *);
enum class kind : unsigned char
{
  a,
  b,
  c
};
using enum kind;
struct spec
{
  kind type : 4;
};
int classify(spec s)
{
  if(s.type == c)
    return 3;
  switch(s.type)
  {
  case a:
    return 1;
  case kind::b:
    return 2;
  default:
    return 0;
  }
}
int main()
{
  spec s{kind::b};
  spec t{c};
  __CPROVER_assert(classify(s) == 2 && classify(t) == 3, "bit-field");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
