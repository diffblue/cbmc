// C++23 multidimensional subscript operator
struct Matrix
{
  int data[4];
  // Multi-parameter operator[] (C++23)
  int operator[](int i, int j)
  {
    return data[i * 2 + j];
  }
};

int main()
{
  Matrix m;
  m.data[0] = 10;
  m.data[1] = 20;
  m.data[2] = 30;
  m.data[3] = 40;
  // Call operator[] with two arguments via method syntax
  int r = m.operator[](1, 0);
  __CPROVER_assert(r == 30, "m[1,0]==30");
  return 0;
}
