// this is a GCC extension

#ifdef __GNUC__
char *strerror(int) __asm("_" "strerror" "$UNIX2003");
int global asm("rax");
asm ("nop");
#endif

#ifdef __GNUC__
// this is something that Apple added to GCC,
// use -fasm-blocks
asm void test();

// likely to mimic CodeWarrior
void asm test()
{
  mov eax, eax
}
#endif

int main()
{
  #ifdef __GNUC__
  __asm volatile("mov ax, dx");

  // another gcc-extension  
  register unsigned my_var asm("eax")=1;
  
  // Apple added "ASM Blocks", similar to MS', to gcc
  __asm {
     mov al, 2
     mov dx, 0xD007
     out dx, al
  }
  #endif

  #ifdef _MSC_VER
  // Microsoft only
  __asm {
     mov al, 2
     mov dx, 0xD007
     out dx, al
  }

  // alternative syntax:
  __asm mov al, 2
  __asm mov dx, 0xD007
  __asm out dx, al
  #endif
  
  return 0;
}
