constexpr int some_number = 10;

// good as array indicies and enums
int my_array[some_number];
enum { E1 = some_number };

constexpr int some_function(int a)
{
  return a+1;
}

constexpr int some_other_value =
  some_function(1);

static_assert(some_other_value == 2, "some_other_value == 2");

constexpr int some_function2(int a)
{
  int b;
  a = a + 1;
  b = a;
  return b + 1;
}

constexpr int some_other_value2 = some_function2(1);

static_assert(some_other_value2 == 3, "some_other_value == 2");

int main()
{
}
