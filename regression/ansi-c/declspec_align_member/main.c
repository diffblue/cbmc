// Visual Studio accepts __declspec in the declaration of a member
struct M1
{
  char c;
  __declspec(align(16)) int i;
};
struct M2
{
  char c;
  __declspec(align(8)) struct N
  {
    char d;
  } n;
};
struct M3
{
  char c;
  __declspec(align(4)) __declspec(align(8)) char a[2], b;
};

_Static_assert(sizeof(struct M1) == 32 && __alignof(struct M1) == 16, "M1");
_Static_assert(sizeof(struct N) == 8 && sizeof(struct M2) == 16, "M2");
_Static_assert(sizeof(struct M3) == 24, "M3");

int main()
{
  return 0;
}
