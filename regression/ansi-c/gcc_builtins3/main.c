// Debian package wine

// http://reviews.llvm.org/D1623 - but apparently not yet in Apple's version
#if defined(__GNUC__) && !defined(__clang__)
// from LLVM test/Sema/varargs-x86-64.c
void __attribute__((ms_abi)) bar(__builtin_ms_va_list authors, ...)
{
  __builtin_ms_va_start (authors, authors);
  (void)__builtin_va_arg(authors, int);
  __builtin_ms_va_end (authors);
}
#endif

int main()
{
}
