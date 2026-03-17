// C++23 multidimensional subscript operator
struct Matrix
{
  int data[3][3];
  int &operator[](int i, int j)
  {
    return data[i][j];
  }
};

int main()
{
  Matrix m{};
  m[1, 2] = 42;
  __CPROVER_assert(m[1, 2] == 42, "multidim subscript");
}
