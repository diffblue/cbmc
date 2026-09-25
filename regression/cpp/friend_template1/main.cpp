template <typename T>
T make(T x);

struct S
{
  template <typename T>
  friend T make(T x);

private:
  int val;
};

int main()
{
  return 0;
}
