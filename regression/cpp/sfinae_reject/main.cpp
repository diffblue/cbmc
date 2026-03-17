// SFINAE: template with enable_if constraint should be rejected
// when the constraint cannot be satisfied.
template <bool B, typename T = void>
struct enable_if
{
};

template <typename T>
struct enable_if<true, T>
{
  typedef T type;
};

template <bool B, typename T = void>
using enable_if_t = typename enable_if<B, T>::type;

struct iterator_tag
{
};

template <typename T>
struct is_iterator
{
  static const bool value = false;
};

template <>
struct is_iterator<int *>
{
  static const bool value = true;
};

// Template with SFINAE constraint
template <typename Iter, typename = enable_if_t<is_iterator<Iter>::value>>
void process(Iter, Iter)
{
}

// Non-template overload
void process(int, int)
{
}

int main()
{
  // Should call non-template overload (SFINAE rejects template)
  process(1, 2);
  return 0;
}
