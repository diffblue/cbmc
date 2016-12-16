
typedef union
{
  int x;
  float y;
} MYUNION;

void fun()
{
  MYUNION myunion_var = {.y = 2.1f}, another_myunion_var = {.y = 2.1f};
}
