// N5008 [dcl.constexpr] (P0784, C++20 constexpr destructors): a
// constexpr destructor's SIDE EFFECTS must not be dropped.  The shape
// of libc++ vector's _ConstructTransaction: the destructor commits
// the container's new end pointer; marking constexpr members as
// constant-fold candidates swallowed the body and every
// initializer-list/range vector construction silently produced size 0
// under --cpp20 (correct under --cpp17, where the destructor is not
// constexpr).
extern "C" void __CPROVER_assert(bool, const char *);
template <class T> struct vec
{
  T *end_;
  T buf[4];
  struct Tx
  {
    constexpr explicit Tx(vec &v, long n) : v_(v), pos_(v.end_), new_end_(v.end_ + n)
    {
    }
    constexpr ~Tx()
    {
      v_.end_ = pos_;
    }
    vec &v_;
    T *pos_;
    T *const new_end_;

  private:
    Tx(Tx const &);
    Tx &operator=(Tx const &);
  };
  vec() : end_(buf)
  {
  }
  void push3()
  {
    Tx tx(*this, 3);
    tx.pos_ = tx.pos_ + 3;
  }
  long size()
  {
    return end_ - buf;
  }
};
int main()
{
  vec<int> v;
  v.push3();
  __CPROVER_assert(v.size() == 3, "transaction committed");
  return 0;
}
