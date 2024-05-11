#ifdef __GNUC__
typedef int my_int16_t __attribute__((__mode__(__HI__)));
static_assert(sizeof(my_int16_t) == 2, "16 bit");

template <std::size_t _Align = __alignof__(int)>
struct __attribute__((__aligned__((_Align))))
{
} __align;
#endif

int main()
{
  return 0;
}
