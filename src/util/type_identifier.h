#pragma once

#include <string>
#include <type_traits>

class type_identifiert final
{
private:
  static int identifier_counter;
  int id;
  explicit type_identifiert(int id) : id(id)
  {
  }

public:
  type_identifiert(const type_identifiert &) = default;
  type_identifiert(type_identifiert &&) = default;
  type_identifiert &operator=(const type_identifiert &) = default;
  type_identifiert &operator=(type_identifiert &&) = default;

  bool operator==(const type_identifiert &other) const;

  bool operator!=(const type_identifiert &other) const;

  template <typename T>
  static type_identifiert get()
  {
    static int t_id = identifier_counter++;
    return type_identifiert{t_id};
  }

#ifdef DEBUG
  std::string debug() const
  {
    return std::string("[id = ") + std::to_string(id) + "]";
  }
#endif
};

struct has_type_indext
{
  void *match_type_identifier(const type_identifiert &id)
  {
    const has_type_indext *cthis = this;
    return const_cast<void *>(cthis->match_type_identifier(id));
  }
  virtual const void *match_type_identifier(const type_identifiert &) const = 0;
};

template <typename T, typename U>
auto fake_dynamic_cast(U *ptr) -> typename std::enable_if<
  std::is_base_of<has_type_indext, U>::value && std::is_pointer<T>::value,
  T>::type
{
  using Tpointee =
    typename std::remove_cv<typename std::remove_pointer<T>::type>::type;
  return static_cast<T>(
    ptr->match_type_identifier(type_identifiert::get<Tpointee>()));
}
