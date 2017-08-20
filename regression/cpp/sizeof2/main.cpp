template <class T>
class A {};

template <class T>
int size()
{
  sizeof(T);
  return 0;
}

int main()
{
  size<int>();

  return 0;
}
