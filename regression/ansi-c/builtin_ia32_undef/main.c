int main()
{
  #ifdef __clang__
  long long A __attribute__ ((__vector_size__ (16))) =
    __builtin_ia32_undef128();
  long long B __attribute__ ((__vector_size__ (32))) =
    __builtin_ia32_undef256();
  long long C __attribute__ ((__vector_size__ (64))) =
    __builtin_ia32_undef512();
  #endif
}
