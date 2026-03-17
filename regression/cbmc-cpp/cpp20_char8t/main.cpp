// C++20 char8_t
int main()
{
  char8_t c = u8'A';
  __CPROVER_assert(c == 65, "char8_t");
  return 0;
}
