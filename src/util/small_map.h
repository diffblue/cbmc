/*******************************************************************\

Module: Small map

Author: Daniel Poetzl

\*******************************************************************/

/// \file
/// Small map

#ifndef CPROVER_UTIL_SMALL_MAP_H
#define CPROVER_UTIL_SMALL_MAP_H

#include <bitset>
#include <cstdint>
#include <cstring>
#include <limits>
#include <memory>
#include <new>
#include <type_traits>
#include <utility>

#include "invariant.h"

//#define _SMALL_MAP_REALLOC_STATS

// The following templates are used by the class below to compute parameters at
// compilation time. When having a compiler that supports constexpr, the
// parameters are computed via static methods defined within the class.
#if !defined(__GNUC__) && _MSC_VER < 1900

template <std::size_t N>
struct num_bitst
{
  static const std::size_t value = 1 + num_bitst<(N >> 1)>::value;
};

template <>
struct num_bitst<1>
{
  static const std::size_t value = 1;
};

template <>
struct num_bitst<0>
{
  static const std::size_t value = 1;
};

template <typename T, std::size_t B, typename U = std::integral_constant<T, 1>>
struct indicator_maskt
{
  static const T value =
    U::value |
    indicator_maskt<T, B, std::integral_constant<T, (U::value << B)>>::value;
};

template <typename T, std::size_t B>
struct indicator_maskt<T, B, std::integral_constant<T, 0>>
{
  static const T value = 0;
};

#endif

/// Map from small integers to values
///
/// A data structure that maps small integers (in {0, ..., Num-1}) to values.
/// It is designed to be more memory-efficient than std::map for this use case.
///
/// In the following we give some data about the memory consumption of
/// small_mapt compared to std::map, on a 64-bit Linux system with GNU STL. It
/// was determined with valgrind/massif. We configured the maps as
/// `small_mapt<uint64_t, uint32_t, Num=8>` and `std::map<uint8_t, uint64_t>`.
/// Thus, indices to small_mapt can be in {0, ..., 7} for this configuration.
///
/// Below we give the memory consumption (in bytes) of small_mapt and std::map,
/// both for when containing 8 elements, and when being empty. The value for
/// "useful" indicates the number of bytes requested, the value for "total" also
/// includes padding bytes.
///
/// small_mapt:
/// - 8 elements:
///   * useful:  80 B
///   * total:  120 B
/// - empty:
///   * useful:  16 B
///   * total:   32 B
///
/// std::map:
/// - 8 elements:
///   * useful: 432 B
///   * total:  512 B
/// - empty:
///   * useful:  48 B
///   * total:   64 B
///
/// \tparam T: mapped type
/// \tparam Ind: unsigned integer type, used to map integer indices to internal
///   indices that index into the memory block that stores the mapped values
/// \tparam Num: gives range of valid indices, i.e., the valid indices are {0,
///   ..., Num-1}, must satisfy Num * num_bits(Num-1) + Num < sizeof(Ind) * 8,
///   with num_bits(n) denoting the minimum number of bits required to represent
///   integer n
template <typename T, typename Ind = uint32_t, std::size_t Num = 8>
class small_mapt
{
public:
  small_mapt() : ind(0), p(nullptr)
  {
  }

private:
  static_assert(std::is_unsigned<Ind>::value, "");

  typedef Ind index_fieldt;

  friend void small_map_test();

  // Memory

  void copy(T *dest, const T *src, std::size_t n) const
  {
    for(std::size_t i = 0; i < n; i++)
    {
      new(dest + i) T(*(src + i));
    }
  }

  T *allocate(std::size_t n) const
  {
    if(n == 0)
      return nullptr;

    T *mem = (T *)malloc(sizeof(T) * n);

    if(!mem)
      throw std::bad_alloc();

    return mem;
  }

  T *allocate(T *ptr, std::size_t n) const
  {
    if(n == 0)
      return nullptr;

    // explicitly cast to char * as GCC 8 warns about not using new/delete for
    // class sharing_node_innert<dstringt, std::basic_string<char>,
    // std::equal_to<dstringt> >
    T *mem = (T *)realloc((char *)ptr, sizeof(T) * n);

    if(!mem)
      throw std::bad_alloc();

#ifdef _SMALL_MAP_REALLOC_STATS
    if(ptr == mem)
    {
      realloc_success++;
    }
    else if(ptr != nullptr)
    {
      realloc_failure++;
    }
#endif

    return mem;
  }

public:
  small_mapt(const small_mapt &m) : ind(m.ind), p(m.p)
  {
    if(m.p == nullptr)
    {
      return;
    }

    const std::size_t n = m.size();
    INVARIANT(n > 0, "size is > 0 if data pointer is non-null");

    p = allocate(n);

    copy(p, m.p, n);
  }

  ~small_mapt()
  {
    if(p)
    {
      std::size_t n = size();

      for(std::size_t i = 0; i < n; i++)
      {
        (p + i)->~T();
      }

      free(p);
    }
  }

private:
  // Derived config

  static const std::size_t N_BITS = std::numeric_limits<index_fieldt>::digits;

  static const std::size_t NUM = Num;

  static_assert(NUM >= 2, "");

// When we don't have constexpr
#if !defined(__GNUC__) && _MSC_VER < 1900

  static const std::size_t S_BITS = NUM * num_bitst<NUM - 1>::value + NUM;

  static const std::size_t BITS = num_bitst<NUM - 1>::value + 1;

  static const index_fieldt IND = indicator_maskt<index_fieldt, BITS>::value;

#else

  static constexpr std::size_t num_bits(const std::size_t n)
  {
    return n < 2 ? 1 : 1 + num_bits(n >> 1);
  }

  static constexpr std::size_t S_BITS = NUM * num_bits(NUM - 1) + NUM;

  static const std::size_t BITS = num_bits(NUM - 1) + 1;

  static constexpr index_fieldt indicator_mask(const index_fieldt digit = 1)
  {
    return !digit ? 0 : digit | indicator_mask(digit << BITS);
  }

  static const index_fieldt IND = indicator_mask();

#endif

  static const index_fieldt MASK = ((index_fieldt)1 << BITS) - 1;

  static_assert(S_BITS <= N_BITS, "");

  static_assert(std::numeric_limits<unsigned>::digits >= BITS, "");

  // Internal

  unsigned get_field(std::size_t field) const
  {
    PRECONDITION(field < NUM);

    unsigned shift = field * BITS;
    return (ind & (MASK << shift)) >> shift;
  }

  void set_field(std::size_t field, unsigned v)
  {
    PRECONDITION(field < NUM);
    PRECONDITION((std::size_t)(v >> 1) < NUM);

    unsigned shift = field * BITS;

    ind &= ~((index_fieldt)MASK << shift);
    ind |= v << shift;
  }

  void shift_indices(std::size_t ii)
  {
    for(std::size_t idx = 0; idx < S_BITS / BITS; idx++)
    {
      unsigned v = get_field(idx);
      if(v & 1)
      {
        v >>= 1;
        if(v > ii)
        {
          v = ((v - 1) << 1) | 1;
          set_field(idx, v);
        }
      }
    }
  }

public:
  // Standard const iterator

  typedef std::pair<const unsigned, const T &> value_type;

  /// Const iterator
  ///
  /// Any modification of the underlying map invalidates the iterator
  class const_iterator
  {
  public:
    explicit const_iterator(const small_mapt &m) : m(m), idx(0), ii(0)
    {
      find_next();
    }

    const_iterator(
      const small_mapt &m,
      const std::size_t idx,
      const std::size_t ii)
      : m(m), idx(idx), ii(ii)
    {
    }

    const value_type operator*() const
    {
      return value_type(idx, *(m.p + ii));
    }

    const std::shared_ptr<value_type> operator->() const
    {
      return std::make_shared<value_type>(idx, *(m.p + ii));
    }

    const_iterator operator++()
    {
      idx++;
      find_next();

      return *this;
    }

    const_iterator operator++(int)
    {
      std::size_t old_idx = idx;
      std::size_t old_ii = ii;

      idx++;
      find_next();

      return const_iterator(m, old_idx, old_ii);
    }

    bool operator==(const const_iterator &other) const
    {
      return idx == other.idx;
    }

    bool operator!=(const const_iterator &other) const
    {
      return idx != other.idx;
    }

  private:
    void find_next()
    {
      while(idx < NUM)
      {
        unsigned v = m.get_field(idx);
        if(v & 1)
        {
          ii = v >> 1;
          break;
        }

        idx++;
      }
    }

    const small_mapt &m;
    std::size_t idx;
    std::size_t ii;
  };

  const_iterator begin() const
  {
    return const_iterator(*this);
  }

  const_iterator end() const
  {
    return const_iterator(*this, NUM, 0);
  }

  /// Const value iterator
  ///
  /// Iterates over the mapped values (in an unspecified order).
  ///
  /// Any modification of the underlying map invalidates the iterator
  class const_value_iterator
  {
  public:
    const_value_iterator(const small_mapt &m, const int ii) : m(m), ii(ii)
    {
    }

    const T &operator*() const
    {
      return *(m.p + ii);
    }

    const T *operator->() const
    {
      return m.p + ii;
    }

    const_value_iterator operator++()
    {
      ii--;

      return *this;
    }

    const_value_iterator operator++(int)
    {
      int old_ii = ii;

      ii--;

      return const_value_iterator(m, old_ii);
    }

    bool operator==(const const_value_iterator &other) const
    {
      return ii == other.ii;
    }

    bool operator!=(const const_value_iterator &other) const
    {
      return ii != other.ii;
    }

  private:
    const small_mapt &m;
    int ii;
  };

  const_value_iterator value_begin() const
  {
    return const_value_iterator(*this, size() - 1);
  }

  const_value_iterator value_end() const
  {
    return const_value_iterator(*this, -1);
  }

  // Interface

  T &operator[](std::size_t idx)
  {
    PRECONDITION(idx < NUM);

    unsigned v = get_field(idx);
    if(v & 1)
    {
      std::size_t ii = v >> 1;
      return *(p + ii);
    }

    std::size_t ii = size();
    p = allocate(p, ii + 1);
    new(p + ii) T();

    v = (ii << 1) | 1;
    set_field(idx, v);

    return *(p + ii);
  }

  const_iterator find(std::size_t idx) const
  {
    PRECONDITION(idx < NUM);

    unsigned v = get_field(idx);
    if(v & 1)
    {
      std::size_t ii = v >> 1;
      return const_iterator(*this, idx, ii);
    }

    return end();
  }

  std::size_t erase(std::size_t idx)
  {
    PRECONDITION(idx < NUM);

    unsigned v = get_field(idx);

    if(v & 1)
    {
      std::size_t ii = v >> 1;

      (p + ii)->~T();
      std::size_t n = size();
      if(ii < n - 1)
      {
        // explicitly cast to char * as GCC 8 warns about not using new/delete
        // for
        // class sharing_node_innert<dstringt, std::basic_string<char>,
        // std::equal_to<dstringt> >
        memmove((char *)(p + ii), p + ii + 1, sizeof(T) * (n - ii - 1));
      }

      p = allocate(p, n - 1);

      if(n == 1)
      {
        p = nullptr;
      }

      set_field(idx, 0);
      shift_indices(ii);

      return 1;
    }

    return 0;
  }

  small_mapt *copy_and_erase(std::size_t idx) const
  {
    PRECONDITION(idx < NUM);

    unsigned v = get_field(idx);
    INVARIANT(v & 1, "element must be in map");

    std::size_t ii = v >> 1;
    std::size_t n = size();

    // new map

    small_mapt *m = new small_mapt();

    if(n == 1)
    {
      return m;
    }

    m->p = allocate(n - 1);

    // copy part before erased element
    copy(m->p, p, ii);

    // copy part after erased element
    copy(m->p + ii, p + ii + 1, n - ii - 1);

    m->ind = ind;
    m->set_field(idx, 0);
    m->shift_indices(ii);

    return m;
  }

  small_mapt *copy_and_insert(std::size_t idx, const T &value) const
  {
    PRECONDITION(idx < NUM);

    unsigned v = get_field(idx);
    INVARIANT(!(v & 1), "element must not be in map");

    std::size_t n = size();
    std::size_t ii = n;

    small_mapt *m = new small_mapt();

    m->p = allocate(n + 1);

    // copy old elements
    copy(m->p, p, n);

    // new element
    new(m->p + ii) T(value);

    m->ind = ind;
    v = (ii << 1) | 1;
    m->set_field(idx, v);

    return m;
  }

  std::size_t size() const
  {
    std::bitset<N_BITS> bs(ind & IND);
    return bs.count();
  }

  bool empty() const
  {
    return !ind;
  }

#ifdef _SMALL_MAP_REALLOC_STATS
  mutable std::size_t realloc_failure = 0;
  mutable std::size_t realloc_success = 0;
#endif

private:
  index_fieldt ind;
  T *p;
};

#endif
