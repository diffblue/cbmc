void *memchr(const void *, int, __CPROVER_size_t n);

int main()
{
  int x;
  memchr(&x, 123, sizeof x);       // safe
  memchr(&x, 123, (sizeof x) + 1); // unsafe
}
