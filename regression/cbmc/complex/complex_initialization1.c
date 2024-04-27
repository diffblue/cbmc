_Complex float var1 = 1 + 2i;
_Complex float var2 = {1, 2};
_Complex float var3 = {1 + 2i};
_Complex float var4 = {1 + 3i, 2};

int main(void)
{
  __CPROVER_assert(var1 == var2, "var1 vs var2");
  __CPROVER_assert(var1 == var3, "var1 vs var3");
  __CPROVER_assert(var1 == var4, "var1 vs var4");
  return 0;
}
