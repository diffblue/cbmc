// C++23 multidimensional subscript
struct Matrix
{
  int data[4];
  int operator[](int i, int j)
  {
    return data[i * 2 + j];
  }
};
int main()
{
  Matrix m;
  m.data[0] = 1;
  m.data[1] = 2;
  m.data[2] = 3;
  m.data[3] = 4;
  int r = m[1, 0];
  __CPROVER_assert(r == 3, "multidim subscript");
  return 0;
}
