struct S
{
  struct
  {
    int : 1;
    int;
    int named;
  };
};

struct S s = {.named = 0};

int main()
{
}
