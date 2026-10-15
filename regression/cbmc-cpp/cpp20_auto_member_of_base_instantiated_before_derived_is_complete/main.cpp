namespace std
{
template <typename _Iter>
concept input_or_output_iterator = requires(_Iter __i)
{
  __i;
};
namespace ranges::__cust_access
{
template <typename _Tp>
concept __member_begin = requires(_Tp __t)
{
  {
    __t.begin
    } -> input_or_output_iterator;
  __t;
};
} // namespace ranges::__cust_access
namespace ranges
{
template <typename>
bool enable_borrowed_range;
template <typename _Tp>
concept __maybe_borrowed_range = enable_borrowed_range<_Tp>;
namespace __cust_access
{
struct _Begin
{
  template <__maybe_borrowed_range _Tp>
  requires __member_begin<_Tp> auto operator()(_Tp &&);
};
} // namespace __cust_access
__cust_access::_Begin begin;
int end;
template <typename>
concept range = requires
{
  end;
};
template <typename _Derived>
struct view_interface
{
  _Derived &_M_derived();
  auto front()
  {
    begin(_M_derived());
  }
};
template <range _Range>
struct ref_view : view_interface<ref_view<_Range>>
{
  _Range begin;
};
} // namespace ranges
} // namespace std
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  // [temp.inst]/11, [dcl.spec.auto.general]/12: view_interface's front() is
  // never used, so its body (whose return type would be deduced from it) is
  // not instantiated; ref_view<int> is complete here and has a member begin
  __CPROVER_assert(
    std::ranges::__cust_access::__member_begin<std::ranges::ref_view<int> &>,
    "member begin found");
  __CPROVER_assert(
    !std::ranges::__cust_access::__member_begin<std::ranges::ref_view<int> &>,
    "WRONG (must FAIL)");
}
