extern "C" void __CPROVER_assert(bool, const char *);
struct limb
{
  int size;
  long *data;
};
typedef limb number[1];
struct holder
{
  limb parts[2];
};
int main()
{
  // `->' on an array: the array-to-pointer conversion yields a pointer to
  // its first element
  number n;
  long storage[2] = {7, 8};
  n->data = storage;
  n->size = 2;
  __CPROVER_assert(n[0].size == 2 && n[0].data[1] == 8, "array of one");
  holder h;
  h.parts->size = 1;
  (h.parts + 1)->size = 2;
  __CPROVER_assert(h.parts[0].size == 1 && h.parts[1].size == 2, "member");
  const limb c[1] = {{3, nullptr}};
  __CPROVER_assert(c->size == 3, "const array");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
