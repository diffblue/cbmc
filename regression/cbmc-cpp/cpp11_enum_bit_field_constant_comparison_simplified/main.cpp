// N5008 [class.bit]/4: a bit-field may have enumeration type.  A comparison
// of such a bit-field's constant value is decided during symbolic
// execution, so the loop in the untaken branch is not unwound (libstdc++
// 13 <format> branches on _Spec<C>::_M_type, a bit-field of type
// _Pres_type).
extern "C" void __CPROVER_assert(bool, const char *);

enum presentation : unsigned char
{
  pres_none,
  pres_d,
  pres_c = 7
};

struct spec
{
  presentation type : 4;
};

int calls = 0;

int main()
{
  spec s{};
  s.type = pres_d;
  if(s.type == pres_c)
  {
    for(int i = 0; i < 1000; ++i)
      ++calls;
  }
  __CPROVER_assert(calls == 0, "branch not taken");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
