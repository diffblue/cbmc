extern "C" void __CPROVER_assert(bool, const char *);
struct emptyt
{
};
int main()
{
  __CPROVER_assert(sizeof(emptyt) >= 1, "empty struct has size >= 1");
  return 0;
}
