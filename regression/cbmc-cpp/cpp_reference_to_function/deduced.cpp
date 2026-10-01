extern "C" void __CPROVER_assert(bool, const char *);
int hit;
void cb(int k)
{
  hit = k;
}
// [temp.deduct.call]/2-3: P = T & is a reference type, so the argument's
// type A is the function type void(int) -- the function-to-pointer
// conversion applies only to a non-reference P -- and T = void(int)
template <class T>
void call_deduced(T &f)
{
  f(3);
}
int main()
{
  call_deduced(cb);
  __CPROVER_assert(hit == 3, "deduced parameter");
  __CPROVER_assert(hit != 3, "WRONG (must FAIL)");
}
