extern int __CPROVER_rounding_mode;

void __asm_fstcw(void *dest)
{
  *(unsigned short *)dest = __CPROVER_rounding_mode << 10;
}

int main()
{
  unsigned short cw;
  __asm { fstcw cw; }
  __CPROVER_assert((cw & 0xc00) == 0, "default rounding mode");
  // fesetround(FE_UPWARD);
  __CPROVER_rounding_mode = 2;
  __asm { fstcw cw; }
  __CPROVER_assert((cw & 0xc00) == 0x800, "round upwards");
}
