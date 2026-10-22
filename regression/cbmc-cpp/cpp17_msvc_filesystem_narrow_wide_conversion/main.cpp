// N5008 [fs.path.type.cvt]/1, [lex.charset]/2: constructing a path from a
// narrow string converts it to the native wide encoding; the characters of
// the basic character set keep their values.  The shape of the MSVC STL:
// the conversion is __std_fs_convert_narrow_to_wide of its runtime library
// (xfilesystem_abi.h), called once for the length and once to convert.
extern "C" void __CPROVER_assert(bool, const char *);
enum class __std_win_error : unsigned long
{
  _Success = 0,
  _Insufficient_buffer = 122,
  _No_unicode_translation = 1113
};
enum class __std_code_page : unsigned int
{
  _Utf8 = 65001
};
struct __std_fs_convert_result
{
  int _Len;
  __std_win_error _Err;
};
extern "C" __std_fs_convert_result __std_fs_convert_narrow_to_wide(
  __std_code_page _Code_page,
  const char *_Input_str,
  int _Input_len,
  wchar_t *_Output_str,
  int _Output_len) noexcept;
extern "C" __std_fs_convert_result __std_fs_convert_wide_to_narrow(
  __std_code_page _Code_page,
  const wchar_t *_Input_str,
  int _Input_len,
  char *_Output_str,
  int _Output_len) noexcept;
int main()
{
  const char narrow[] = "a.txt";
  const auto length = __std_fs_convert_narrow_to_wide(
    __std_code_page::_Utf8, narrow, 5, nullptr, 0);
  __CPROVER_assert(
    length._Len == 5 && length._Err == __std_win_error::_Success, "length");
  wchar_t wide[5];
  const auto converted =
    __std_fs_convert_narrow_to_wide(__std_code_page::_Utf8, narrow, 5, wide, 5);
  __CPROVER_assert(
    converted._Len == 5 && wide[0] == L'a' && wide[4] == L't', "converted");
  char back[5];
  __std_fs_convert_wide_to_narrow(__std_code_page::_Utf8, wide, 5, back, 5);
  __CPROVER_assert(back[1] == '.', "back");
  __CPROVER_assert(wide[1] == L'x', "WRONG (must FAIL)");
  return 0;
}
