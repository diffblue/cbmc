int main()
{
  // A wide character constant has type wchar_t (C11 6.4.4.4p11).
  __CPROVER_assert((__typeof__(L'a'))-1 > 0, "wchar_t is unsigned");
  return 0;
}
