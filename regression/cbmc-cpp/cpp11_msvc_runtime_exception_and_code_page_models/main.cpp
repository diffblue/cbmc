// The MSVC runtime functions that std::exception and std::filesystem::path
// call, declared as in vcruntime_exception.h and xfilesystem_abi.h; their
// definitions are in the runtime library.
// N5008 [exception]/2: an exception and its copy have equal what() strings.
// [fs.path.type.cvt]/1: the native narrow encoding is the operating
// system's current one.
extern "C" void __CPROVER_assert(bool, const char *);
extern "C" void *malloc(decltype(sizeof(0)));
extern "C" void free(void *);
struct __std_exception_data
{
  char const *_What;
  bool _DoFree;
};
extern "C" void __std_exception_copy(
  __std_exception_data const *_From,
  __std_exception_data *_To);
extern "C" void __std_exception_destroy(__std_exception_data *_Data);
enum class __std_code_page : unsigned int
{
  _Acp = 0,
  _Utf8 = 65001
};
extern "C" __std_code_page __std_fs_code_page() noexcept;

int main()
{
  // a message the exception owns is copied
  __std_exception_data owned = {"bad cast", true};
  __std_exception_data copy = {nullptr, false};
  __std_exception_copy(&owned, &copy);
  if(copy._What != nullptr)
  {
    __CPROVER_assert(copy._DoFree, "an owned copy");
    __CPROVER_assert(copy._What != owned._What, "a fresh copy");
    __CPROVER_assert(
      copy._What[0] == 'b' && copy._What[3] == ' ' && copy._What[8] == 0,
      "the same string");
  }
  __std_exception_destroy(&copy);
  __CPROVER_assert(copy._What == nullptr && !copy._DoFree, "destroyed");

  // a message the exception does not own is shared
  __std_exception_data shared = {"static", false};
  __std_exception_data alias = {nullptr, true};
  __std_exception_copy(&shared, &alias);
  __CPROVER_assert(alias._What == shared._What && !alias._DoFree, "shared");
  __std_exception_destroy(&alias);

  __std_code_page page = __std_fs_code_page();
  __CPROVER_assert(
    page == __std_code_page::_Acp || page != __std_code_page::_Acp,
    "a code page");
  __CPROVER_assert(page == __std_code_page::_Utf8, "WRONG (must FAIL)");
  return 0;
}
