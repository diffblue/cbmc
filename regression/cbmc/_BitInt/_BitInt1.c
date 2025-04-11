// _BitInt is a C23 feature

// sizeof
static_assert(sizeof(unsigned _BitInt(1)) == 1);
static_assert(sizeof(_BitInt(32)) == 4);
static_assert(sizeof(_BitInt(33)) == 8);
static_assert(sizeof(_BitInt(65)) == 16);
static_assert(sizeof(_BitInt(128)) == 16);

int main()
{
  return 0;
}
