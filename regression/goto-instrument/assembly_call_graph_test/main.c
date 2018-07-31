// This is a hack to make the test pass on windows. The way CBMC on
// windows handles assembly code needs to be fixed.
// CBMC doesn't recognise __asm mfence as a function.

#ifndef __GNUC__
void __asm_mfence();
#endif

void* thr(void * arg) {
#ifdef __GNUC__
__asm__ __volatile__ ("mfence": : :"memory");
#else
__asm_mfence();
#endif
}

int main()
{
  thr(0);
}
