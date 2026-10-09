namespace N
{
enum error_type
{
  _S_error_collate,
  _S_error_ctype
};

constexpr error_type error_collate(_S_error_collate);
constexpr error_type error_ctype(_S_error_ctype);
} // namespace N

int main()
{
  __CPROVER_assert(N::error_collate == N::_S_error_collate, "error_collate");
  __CPROVER_assert(N::error_ctype == N::_S_error_ctype, "error_ctype");
  return 0;
}
