void* thr(void * arg) {
#ifdef __GNUC__
__asm__ __volatile__ ("mfence": : :"memory");
#elif defined(_MSC_VER)
__asm mfence;
#endif
}

int main()
{
  thr(0);
}
