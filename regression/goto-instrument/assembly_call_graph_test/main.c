void* thr(void * arg) {
#ifdef __GNUC__
  // gcc/clang syntax
  __asm__ __volatile__("mfence" : : : "memory");
#else
  // this is Visual Studio syntax
  __asm mfence;
#endif
}

int main()
{
  thr(0);
}
