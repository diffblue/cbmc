#define ROUND_F(x) ((int)((x) + 0.5f))
int eight = ROUND_F(100.0f / 12.0f);

int main()
{
  __CPROVER_assert(eight == 8, "assertion eight == 8");
}
