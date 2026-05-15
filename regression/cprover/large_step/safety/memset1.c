void *memset(void *, int, __CPROVER_size_t);

int main()
{
  int x;
  memset(&x, 0, sizeof x);       // safe
  memset(&x, 0, (sizeof x) + 1); // unsafe
}
