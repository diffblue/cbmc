/*******************************************************************\

Module: Overlay-map

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Overlay-map

#ifndef CPROVER_UTIL_OVERLAY_MAP_H
#define CPROVER_UTIL_OVERLAY_MAP_H

#include <map>
#include <iterator>
#include <stdlib.h>
#include <assert.h>

template<class K, class V> struct overlay_map
{
  std::map<K, V> local_map;
  const overlay_map* base_map;
  K removed_key;
  bool removed_key_valid;

  // NOLINTNEXTLINE(readability/identifiers)
  typedef typename std::map<K, V>::value_type itervaltype;
  // NOLINTNEXTLINE(readability/identifiers)
  typedef typename std::map<K, V>::iterator localiter;
  // NOLINTNEXTLINE(readability/identifiers)
  typedef typename std::map<K, V>::const_iterator localciter;

  overlay_map() : base_map(0), removed_key_valid(false) {}

  void set_base(const overlay_map* other)
  {
    local_map.clear();
    base_map=other;
  }

  const overlay_map* get_base() const { return base_map; }

  const V &at(K key) const
  {
    if(removed_key_valid && key==removed_key)
      throw "overlay_map::at against deleted key";
    else if(!base_map)
      return local_map.at(key);
    else
      {
        localciter findit=local_map.find(key);
        if(findit!=local_map.end())
          return findit->second;
        return base_map->at(key);
      }
  }

  V &operator[](const K key)
  {
    return local_map[key];
  }

  std::pair<localiter, bool> insert(const itervaltype &newkv)
  {
    return local_map.insert(newkv);
  }

  size_t size() const
  {
    // TODO: improve this!
    size_t count=0;
    auto it=cbegin(), itend=cend();
    for(; it!=itend; ++it, ++count) {}
    return count;
  }

  bool empty() const { return size()==0; }

  // NOLINTNEXTLINE(readability/identifiers)
  class const_iterator:
    public std::iterator<std::forward_iterator_tag, const itervaltype>
  {
    localciter localmapit, localmapend;
    const_iterator *basemapitp;
    K removekey;
    bool removekeyvalid;
    bool _is_end;
  public:
    explicit const_iterator(
      localciter _localmapit,
      localciter _localmapend,
      const const_iterator &_basemapit,
      K _removekey,
      bool _removekeyvalid) :
      localmapit(_localmapit),
      localmapend(_localmapend),
      removekey(_removekey),
      removekeyvalid(_removekeyvalid),
      _is_end(false)
    {
      basemapitp=new const_iterator(_basemapit);
      skip_removed_keys();
      check_is_end();
    }

    explicit const_iterator(
      localciter _localmapit,
      localciter _localmapend,
      const_iterator &&_basemapit,
      K _removekey,
      bool _removekeyvalid) :
      localmapit(_localmapit),
      localmapend(_localmapend),
      removekey(_removekey),
      removekeyvalid(_removekeyvalid),
      _is_end(false)
    {
      basemapitp=new const_iterator(std::move(_basemapit));
      skip_removed_keys();
      check_is_end();
    }

    explicit const_iterator(
      localciter _localmapit,
      localciter _localmapend) :
      localmapit(_localmapit),
      localmapend(_localmapend),
      basemapitp(0),
      _is_end(false)
    {
      check_is_end();
    }

    explicit const_iterator(bool is_end) :
      basemapitp(0),
      removekeyvalid(false),
      _is_end(is_end)
    {}

    const_iterator() :
      basemapitp(0),
      removekeyvalid(false),
      _is_end(false)
    {}

    const_iterator(const const_iterator &other) :
      localmapit(other.localmapit),
      localmapend(other.localmapend),
      removekey(other.removekey),
      removekeyvalid(other.removekeyvalid),
      _is_end(other._is_end)
    {
      if(other.basemapitp)
        basemapitp=new const_iterator(*other.basemapitp);
      else
        basemapitp=0;
    }

    const_iterator(const_iterator &&other) :
      localmapit(std::move(other.localmapit)),
      localmapend(std::move(other.localmapend)),
      removekey(other.removekey),
      removekeyvalid(other.removekeyvalid),
      _is_end(other._is_end)
    {
      basemapitp=other.basemapitp;
      other.basemapitp=0;
    }

    const_iterator &operator=(const const_iterator &other)
    {
      localmapit=other.localmapit;
      localmapend=other.localmapend;
      removekey=other.removekey;
      removekeyvalid=other.removekeyvalid;
      _is_end=other._is_end;
      if(basemapitp)
        delete basemapitp;
      if(other.basemapitp)
        basemapitp=new const_iterator(*other.basemapitp);
      else
        basemapitp=0;
      return *this;
    }

    const_iterator &operator=(const_iterator &&other)
    {
      localmapit=std::move(other.localmapit);
      localmapend=std::move(other.localmapend);
      removekey=other.removekey;
      removekeyvalid=other.removekeyvalid;
      _is_end=other._is_end;
      if(basemapitp)
        delete basemapitp;
      basemapitp=other.basemapitp;
      other.basemapitp=0;
      return *this;
    }

    ~const_iterator()
    {
      if(basemapitp)
        delete basemapitp;
    }

    const_iterator &operator++()
    {
      assert(!_is_end);
      if(basemapitp)
      {
        auto &basemapit=*basemapitp;
        if(localmapit!=localmapend &&
           (!basemapit.is_end()) &&
           localmapit->first==basemapit->first)
        {
          assert(!removekeyvalid);
          ++basemapit; ++localmapit;
        }
        else if(localmapit!=localmapend &&
                (basemapit.is_end() || localmapit->first<basemapit->first))
        {
          assert(!removekeyvalid);
          ++localmapit;
        }
        else
        {
          ++basemapit;
          skip_removed_keys();
        }
      }
      else
        ++localmapit;
      check_is_end();
      return *this;
    }
    const_iterator operator++(int)
    {
      const_iterator retval = *this;
      ++(*this);
      return retval;
    }

    bool operator==(const const_iterator &other) const
    {
      if(_is_end || other._is_end)
        return _is_end == other._is_end;
      if(localmapit!=other.localmapit)
        return false;
      if(basemapitp)
        return other.basemapitp && (*basemapitp)==*(other.basemapitp);
      else
        return true;
    }
    bool operator!=(const const_iterator &other) const
    {
      return !(*this == other);
    }

  private:
    typedef const typename std::map<K, V>::value_type base_mapt;
    typedef std::iterator<std::forward_iterator_tag, base_mapt> base_itert;

  public:
    typename base_itert::reference operator*() const
    {
      if(basemapitp)
      {
        auto &basemapit=*basemapitp;
        if(!basemapit.is_end())
        {
          const auto &baseentry=*basemapit;
          if(localmapit==localmapend || baseentry.first<localmapit->first)
            return baseentry;
        }
      }
      return *localmapit;
    }

    typename base_itert::pointer operator->() const
    {
      return &**this;
    }

    // Returns nonsense if this iterator==end()
    bool points_to_base() const
    {
      if(!basemapitp)
        return false;
      if(basemapitp->is_end())
        return false;
      if(localmapit==localmapend)
        return true;
      return (*basemapitp)->first < localmapit->first;
    }

    void skip_removed_keys()
    {
      assert(basemapitp);
      auto &basemapit=*basemapitp;
      while(removekeyvalid &&
            (!basemapit.is_end()) &&
            basemapit->first==removekey)
      {
        ++basemapit;
      }
    }

    void check_is_end()
    {
      if(localmapit==localmapend && ((!basemapitp) || basemapitp->is_end()))
        _is_end=true;
    }

    bool is_end() const { return _is_end; }
  };

  const_iterator cbegin() const
  {
    if(base_map)
      return const_iterator(local_map.begin(), local_map.end(),
                            base_map->begin(),
                            removed_key, removed_key_valid);
    else
      return const_iterator(local_map.begin(), local_map.end());
  }
  const_iterator begin() const
  {
    return cbegin();
  }
  const_iterator local_begin() const
  {
    return const_iterator(local_map.begin(), local_map.end());
  }

  const_iterator cend() const
  {
    return const_iterator(true);
  }
  const_iterator end() const
  {
    return cend();
  }
  const_iterator local_end() const
  {
    return const_iterator(true);
  }

  const_iterator find(const K key) const
  {
    localciter find1=local_map.find(key);
    if(find1!=local_map.end())
    {
      if(base_map)
        return
          const_iterator(
            find1,
            local_map.end(),
            base_map->lower_bound(key),
            removed_key,
            removed_key_valid);
      else
        return const_iterator(find1, local_map.end());
    }
    else if(base_map)
    {
      const_iterator find2=base_map->find(key);
      if(find2!=base_map->end())
        return
          const_iterator(
            local_map.lower_bound(key),
            local_map.end(),
            std::move(find2),
            removed_key,
            removed_key_valid);
      }
    return end();
  }

  const_iterator lower_bound(const K key) const
  {
    if(base_map)
    {
      return
        const_iterator(
          local_map.lower_bound(key),
          local_map.end(),
          base_map->lower_bound(key),
          removed_key,
          removed_key_valid);
    }
    else
      return const_iterator(local_map.lower_bound(key), local_map.end());
  }

  bool operator==(const overlay_map &other) const
  {
    // Cheap comparison if possible:
    if(base_map == other.base_map)
    {
      if(removed_key_valid)
        return other.removed_key_valid && removed_key == other.removed_key;
      else
        return local_map == other.local_map;
    }

    // Otherwise, compare using iterators so that meaning rather than specific
    // representation is compared-- for example, if this map
    // uses a base but the other doesn't.
    const_iterator
      thisit=begin(),
      otherit=other.begin(),
      thisend=end(),
      otherend=other.end();
    for(; thisit!=thisend && otherit!=otherend; ++thisit, ++otherit)
    {
      if(*thisit!=*otherit)
        return false;
    }
    return thisit==thisend && otherit==otherend;
  }

  void erase(const K _key)
  {
    if(base_map)
    {
      assert(local_map.size()==0);
      assert((!removed_key_valid) || removed_key==_key);
      removed_key=_key;
      removed_key_valid=true;
    }
    else
      local_map.erase(_key);
  }

  size_t map_depth() const
  {
    return 1 + (base_map ? base_map->map_depth() : 0);
  }

  void flatten()
  {
    // If this is an overlay map, flatten the
    // base map into the local and unref it.
    if(!base_map)
      return;
    overlay_map<K, V> flattened;
    for(const auto &kv : *this)
      flattened.insert(kv);
    *this=std::move(flattened);
  }
};

#endif
