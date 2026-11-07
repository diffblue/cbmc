extern "C" void __CPROVER_assert(bool, const char *);
struct flag
{
  int v;
  explicit operator bool() const
  {
    return v != 0;
  }
};
flag make(int v)
{
  return flag{v};
}
int main()
{
  int hits = 0;
  if(flag f = make(3))
    hits += f.v;
  if(flag f = make(0))
    hits += 100;
  int arr[2] = {1, 2};
  if(int *p = arr)
    hits += p[1];
  float x = 2.f;
  if(float a = x)
    hits += static_cast<int>(a);
  if(float a = 0.f)
    hits += 100;
  int k = 3;
  while(int m = k--)
    hits += m;
  __CPROVER_assert(
    hits == 3 + 2 + 2 + 6,
    "conditions that are declarations of class, pointer, float and int type");
  __CPROVER_assert(hits == 12, "WRONG (must FAIL)");
}
