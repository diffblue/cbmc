struct some_struct
{
  int x;
};

struct some_struct function_without_body();

int main()
{
  struct some_struct s = function_without_body();
  return 0;
}
