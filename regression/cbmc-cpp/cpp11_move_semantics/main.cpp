// C++11 move semantics
struct Buffer
{
  int *data;
  int size;
  Buffer(int n) : data(new int[n]), size(n)
  {
    data[0] = 42;
  }
  Buffer(Buffer &&other) : data(other.data), size(other.size)
  {
    other.data = 0;
    other.size = 0;
  }
  ~Buffer()
  {
    delete[] data;
  }
};
int main()
{
  Buffer a(1);
  Buffer b(static_cast<Buffer &&>(a));
  __CPROVER_assert(b.size == 1, "moved size");
  __CPROVER_assert(a.data == 0, "source nulled");
  return 0;
}
