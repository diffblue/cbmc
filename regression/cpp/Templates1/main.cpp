template <typename T1, typename T2>
class basic
{
  T1 some;
  T2 other;
};

template <typename T1x, typename T2x=char>
class basic;

basic<char> b;

int main()
{
}
