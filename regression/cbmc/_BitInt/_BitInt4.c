// _BitInt is a C23 feature

static_assert(6uwb + -6wb == 0);
static_assert(sizeof(255uwb + 1uwb) == 1);
static_assert(sizeof(0b1111'1111uwb) == 1);

int main()
{
  return 0;
}
