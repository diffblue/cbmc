// C++14 variable template: declaration parsing
template <class T>
const bool is_void_v = false;

template <>
const bool is_void_v<void> = true;

template <class T>
inline const bool is_integral_v = false;

int main()
{
  return 0;
}
