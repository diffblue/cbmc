#ifdef __GNUC__
// an asm block as a function body, as with gcc -fasm-blocks
void asm test()
{
  mov eax, eax
}
#endif

int main()
{
#ifdef __GNUC__
  test();
#endif
  return 0;
}
