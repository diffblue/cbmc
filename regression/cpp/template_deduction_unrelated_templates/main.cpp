// Template argument deduction must not match unrelated template
// instantiations. When resolving operator+(a, b) where a and b are
// instances of Str<char>, the function template operator+ for
// move_iter<I> must not deduce I=char from Str<char>.

template <typename I>
struct traits
{
};

template <typename I>
struct traits<I *>
{
  typedef I &reference;
  typedef long difference_type;
};

template <typename I>
class move_iter
{
  typedef typename traits<I>::reference ref;

public:
  typedef typename traits<I>::difference_type difference_type;
};

template <typename I>
move_iter<I>
operator+(typename move_iter<I>::difference_type n, const move_iter<I> &x);

template <typename C>
struct Str
{
  typedef C value_type;
};

Str<char> operator+(const Str<char> &a, const Str<char> &b);

void test()
{
  Str<char> a;
  Str<char> b;
  a + b;
}

int main()
{
  return 0;
}
