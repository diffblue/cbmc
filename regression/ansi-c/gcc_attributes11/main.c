#ifdef __GNUC__
// example extracted from SV-COMP's ldv-linux-3.4-simple/
// 32_7_cpp_false-unreach-call_single_drivers-net-phy-dp83640
static int __attribute__((__section__(".init.text")))
__attribute__((no_instrument_function)) dp83640_init(void)
{
  return 0;
}
int init_module(void) __attribute__((alias("dp83640_init")));
#endif

int main()
{
#ifdef __GNUC__
  dp83640_init();
#endif
  return 0;
}
