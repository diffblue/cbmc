/*******************************************************************\

Module: Memory-efficient unordered_map

Author: Diffblue Ltd.

\*******************************************************************/

#ifndef CPROVER_UTIL_OVERLAY_MAP_H
#define CPROVER_UTIL_OVERLAY_MAP_H

#include <memory>
#include <vector>
#include <unordered_map>

/// "Cheap copy" unordered map
/// Copy-constructor is disabled. Call .overlay() to create a new
/// layer on top of an existing map.
///
/// Copied data is shared with previous instance to avoid copying of
/// all elements stored inside the map. For example having a map with
/// 1000 elements, passing its overlay into the function and modifying one
/// element is an efficient operation.
/// Modifying elements in a base map changes non-overlaid elements in
/// the child map. Destroying base, doesn't destroy elements in an overlay.
template<typename key_type, typename value_type>
class overlay_unordered_mapt
{
public:
  /// Default constructor - constructs empty map
  overlay_unordered_mapt():
    data_(1, std::make_shared<std::unordered_map<key_type, value_type>>())
  { }

  /// Move constructor - claim "other"'s map state. Empty "other" map
  overlay_unordered_mapt(overlay_unordered_mapt &&other):
    overlay_unordered_mapt()
  { *this=std::move(other); }

  /// Convert regular map into overlay map
  explicit overlay_unordered_mapt(
    std::unordered_map<key_type, value_type> &&other):
    data_(
      1,
      std::make_shared<std::unordered_map<key_type, value_type>>(
        std::move(other)))
  { }

  /// Copy assignment - Clear this map and inherit from "other" map
  overlay_unordered_mapt &operator=(const overlay_unordered_mapt &other)=delete;

  overlay_unordered_mapt overlay() const
  { return overlay_unordered_mapt(*this); }

  /// Move assignment - swap state with "other" map
  overlay_unordered_mapt &operator=(overlay_unordered_mapt &&other)
  {
    std::swap(other.data_, data_);
    return *this;
  }

  /// Set value for a specified key
  void set(const key_type &key, value_type value)
  {
    auto &map=*data_.back();
    auto it=map.find(key);
    if(it==map.end())
      map.emplace(key, std::move(value));
    else
      it->second=std::move(value);
  }

  /// Get a value stored under specified key
  value_type &at(const key_type &key)
  { return p_at(data_, key); }

  /// Get a value stored under specified key
  const value_type &at(const key_type &key) const
  { return p_at(data_, key); }

private:
  /// Creates a map that inherits elements with the "other" map
  overlay_unordered_mapt(const overlay_unordered_mapt &other):
    data_(other.data_)
  {
    data_.emplace_back(
      std::make_shared<std::unordered_map<key_type, value_type>>());
  }

  template<typename data_t>
  static auto p_at(data_t &data, const key_type &key)
    -> decltype((*data[0])[key])
  {
    for(auto it=data.rbegin(), end=data.rend(); it!=end; ++it)
    {
      auto &map=(**it);
      const auto pair_it=map.find(key);
      if(pair_it!=map.end())
        return pair_it->second;
    }
    throw std::out_of_range("Element not found");
  }

  typedef
    std::vector<
      std::shared_ptr<
        std::unordered_map<key_type, value_type>>> datat;
  datat data_;
};

#endif // CPROVER_UTIL_OVERLAY_MAP_H
