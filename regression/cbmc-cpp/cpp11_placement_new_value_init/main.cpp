extern "C" void __CPROVER_assert(bool, const char *);
void *operator new(unsigned long, void *) noexcept;
struct podt
{
  int a;
  int b = 5;
};
int main()
{
  int v = 7;
  ::new((void *)&v) int; // default-init: unchanged
  __CPROVER_assert(v == 7, "default-init leaves storage");
  podt p;
  p.a = 3;
  ::new((void *)&p) podt(); // value-init: a zeroed, b from DMI
  __CPROVER_assert(p.a == 0 && p.b == 5, "value-init zero then DMI");
  return 0;
}
