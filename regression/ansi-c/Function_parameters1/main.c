typedef void func_type(int, char);

typedef void func_type2(func_type f, char z);

typedef void func_type3(int size, int array[size]);

void func1(int size, int array[size][size]);

void func1(int size, int array[size][size])
{
}

void func2(int size, int array[static size]);

void func3(int size, int array[const]);

int f()
{
  typedef void func_type_td(int size, int array[size]);
}

int g()
{
  typedef void func_type_td(int size, int array[size]);
}

int main()
{
}
