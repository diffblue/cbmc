// Static data member specialization of a class template
template <typename T>
struct Cache
{
  static const T *data;
};

template <>
const char *Cache<char>::data;

int main()
{
  Cache<char> c;
}
