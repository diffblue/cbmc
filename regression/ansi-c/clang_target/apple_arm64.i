// Apple's Arm platforms deviate from AAPCS64: char and wchar_t are signed.
_Static_assert((char)-1 < 0, "char is signed");
// A wide character constant has type wchar_t (C11 6.4.4.4p11).
_Static_assert((__typeof__(L'a'))-1 < 0, "wchar_t is signed");

int main()
{
  return 0;
}
