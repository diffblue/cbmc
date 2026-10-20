extern "C" void __CPROVER_assert(bool, const char *);
template <class T, template <class...> class Tm>
constexpr bool is_specialization_v = false;
// N5008 [temp.deduct.type]/8, [temp.arg.template]/1: Tm is deduced from
// both `Tm<A...>' and the template template argument; both deductions give
// the class template itself (the MSVC STL's _Is_specialization_v, behind
// chrono::_Is_duration_v)
template <template <class...> class Tm, class... A>
constexpr bool is_specialization_v<Tm<A...>, Tm> = true;
template <class R, class P = int>
class duration;
template <class T>
constexpr bool is_duration_v = is_specialization_v<T, duration>;
template <class R, class P>
class duration
{
};
template <class X>
struct other
{
};
int main()
{
  __CPROVER_assert(
    is_duration_v<duration<long>> && is_specialization_v<other<int>, other> &&
      !is_specialization_v<other<int>, duration> &&
      !is_specialization_v<int, other>,
    "specializations recognised");
  __CPROVER_assert(!is_duration_v<duration<long>>, "WRONG (must FAIL)");
  return 0;
}
