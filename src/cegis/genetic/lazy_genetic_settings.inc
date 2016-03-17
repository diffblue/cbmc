#include <cegis/genetic/lazy_genetic_settings.h>

template<class wrappedt>
lazy_genetic_settingst<wrappedt>::lazy_genetic_settingst(
    const wrappedt &wrapped) :
    wrapped(wrapped)
{
}

template<class wrappedt>
lazy_genetic_settingst<wrappedt>::~lazy_genetic_settingst()
{
}

template<class wrappedt>
size_t lazy_genetic_settingst<wrappedt>::min_prog_sz(const size_t prog_index)
{
  return wrapped.min_prog_sz(prog_index);
}

template<class wrappedt>
size_t lazy_genetic_settingst<wrappedt>::max_prog_sz(size_t prog_index)
{
  return wrapped.max_prog_sz(prog_index);
}

template<class wrappedt>
std::function<size_t(void)> lazy_genetic_settingst<wrappedt>::max_prog_sz_provider()
{
  return [this]()
  { return wrapped.max_prog_sz();};
}

template<class wrappedt>
std::function<size_t(size_t)> lazy_genetic_settingst<wrappedt>::max_prog_sz_per_index_provider()
{
  return [this](const size_t prog_index)
  { return wrapped.max_prog_sz(prog_index);};
}

#define lazy_cache_access(store, source) \
  if (!store.first) \
  { \
    store.second=source(); \
    store.first=true; \
  } \
  return store.second;

template<class wrappedt>
size_t lazy_genetic_settingst<wrappedt>::max_prog_sz()
{
  lazy_cache_access(stored_max_prog_sz, wrapped.max_prog_sz);
}

template<class wrappedt>
size_t lazy_genetic_settingst<wrappedt>::num_progs()
{
  lazy_cache_access(stored_num_progs, wrapped.num_progs);
}

template<class wrappedt>
size_t lazy_genetic_settingst<wrappedt>::num_vars()
{
  lazy_cache_access(stored_num_vars, wrapped.num_vars);
}

template<class wrappedt>
size_t lazy_genetic_settingst<wrappedt>::num_consts()
{
  lazy_cache_access(stored_num_consts, wrapped.num_consts);
}

template<class wrappedt>
std::function<size_t(void)> lazy_genetic_settingst<wrappedt>::num_consts_provder()
{
  return [this]()
  { return wrapped.num_consts();};
}

template<class wrappedt>
size_t lazy_genetic_settingst<wrappedt>::num_x0()
{
  lazy_cache_access(stored_num_x0, wrapped.num_x0);
}
