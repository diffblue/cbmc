extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [class.friend]/6 (note 3): a friend function defined outside the
// class is not in the scope of the class, so the member entry::status does
// not hide fs::status in copy_impl's body (the MSVC STL's
// filesystem::_Copy_impl and _Get_any_status)
namespace fs
{
struct path
{
  int v;
};
inline int status(const path &p, int flags)
{
  return p.v + flags;
}
struct entry
{
  friend int copy_impl(const entry &from, const path &to, int flags);
  path p;

private:
  int status(int flags) const
  {
    return 100 + flags;
  }
};
inline int copy_impl(const entry &from, const path &to, const int flags)
{
  return from.status(flags) + status(to, flags);
}
} // namespace fs
int main()
{
  fs::entry e{{1}};
  fs::path t{2};
  __CPROVER_assert(copy_impl(e, t, 3) == 108, "friend definition");
  __CPROVER_assert(copy_impl(e, t, 3) == 0, "WRONG (must FAIL)");
}
