// N5008 [meta.trans.other] common_reference over differing reference kinds.
#include <concepts>

struct W
{
  int v = 0;
};

int main()
{
  static_assert(
    std::is_same_v<std::common_reference_t<int &, int &&>, const int &>,
    "int&, int&&");
  static_assert(
    std::is_same_v<std::common_reference_t<int &&, const int &>, const int &>,
    "int&&, const int&");
  static_assert(
    std::is_same_v<std::common_reference_t<int &&, int &&>, int &&>,
    "int&&, int&&");
  static_assert(
    std::is_same_v<std::common_reference_t<W &, W &&>, const W &>, "W&, W&&");
  static_assert(
    std::is_same_v<std::common_reference_t<W &&, const W &>, const W &>,
    "W&&, const W&");
  static_assert(
    std::is_same_v<std::common_reference_t<int &, long &>, long>,
    "different types: common_type");
  static_assert(std::common_reference_with<int &, int &&>, "with int&, int&&");
  static_assert(std::common_reference_with<W &&, W &>, "with W&&, W&");
  return 0;
}
