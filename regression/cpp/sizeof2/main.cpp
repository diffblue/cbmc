template <class T>
class A {};

template <class T>
int size()
{
  sizeof(T);
}

int main()
{
  size<int>();
}
