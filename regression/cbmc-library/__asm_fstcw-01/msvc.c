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
