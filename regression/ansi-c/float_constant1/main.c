#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1];    

STATIC_ASSERT(0x1.0p-95f == 2.524355e-29f);

int main()
{
}
