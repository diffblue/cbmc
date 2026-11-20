// N5008 [res.on.data.races]/1-3: the standard library prevents data races
// on its internal objects; [locale.id]/1: an id is an index for lookup, so
// one id has one index.  The MSVC STL's locale::id::_Get_index (xlocale)
// assigns the index from the static counter _Id_cnt under the runtime's lock
// _Lockit (yvals.h).  cbmc models _Lockit as doing nothing, valid only for a
// single thread (cpp_typecheck_stdlib.cpp); with two threads both may see
// _Id == 0 and assign different indices.  The two classes, reduced.
namespace std
{
typedef decltype(sizeof(0)) size_t;
class _Lockit
{
public:
  explicit _Lockit(int);
  ~_Lockit();
};
class locale
{
public:
  class id
  {
  public:
    size_t _Get_index()
    {
      if(_Id == 0)
      {
        _Lockit _Lock(0);
        if(_Id == 0)
          _Id = static_cast<size_t>(++_Id_cnt);
      }
      return _Id;
    }

  private:
    size_t _Id = 0;
    static int _Id_cnt;
  };
};
} // namespace std
extern "C" void __CPROVER_assert(bool, const char *);
std::locale::id facet_id;
std::size_t in_thread;
bool thread_done;
int main()
{
__CPROVER_ASYNC_1:
{
  in_thread = facet_id._Get_index();
  thread_done = true;
}
  std::size_t here = facet_id._Get_index();
  if(thread_done)
    __CPROVER_assert(here == in_thread, "one index per id");
  __CPROVER_assert(here == 0, "WRONG (must FAIL)");
  return 0;
}
