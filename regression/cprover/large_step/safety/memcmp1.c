int memcmp(const void *, const void *, __CPROVER_size_t);

int main()
{
  int x;
  memcmp(&x, &x, sizeof x);       // safe
  memcmp(&x, &x, (sizeof x) + 1); // unsafe
}
