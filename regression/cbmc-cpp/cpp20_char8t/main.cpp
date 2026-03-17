// C++20 char8_t
int main()
{
  char8_t c = u8'a';
  __CPROVER_assert(c == 97, "u8'a'==97");
  return 0;
}
