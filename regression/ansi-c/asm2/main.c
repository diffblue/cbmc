// this is a GCC extension

int main()
{
  int x, y;
#ifdef __GNUC__
  asm goto ("jc %l[error];"
      : : "r"(x), "r"(&y) : "memory" : error);
  asm
#   11
    __inline volatile("jc %l[error];"
                      :
                      : "r"(x), "r"(&y)
                      : "memory"
                      : error);
#endif
error:
  return 0;
}
