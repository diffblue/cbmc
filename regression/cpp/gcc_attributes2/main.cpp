#ifdef __GNUC__
typedef int my_int16_t __attribute__((__mode__(__HI__)));
static_assert(sizeof(my_int16_t) == 2, "16 bit");
#endif

int main()
{
  return 0;
}
