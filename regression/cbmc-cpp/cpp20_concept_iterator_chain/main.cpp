// C++20 iterator concepts evaluated over a *class* iterator (not just a
// pointer).  This exercises the deep concept chain
// (random_access_iterator -> ... -> totally_ordered, sized_sentinel_for,
// semiregular -> copyable -> movable -> swappable -> assignable_from -> ...)
// over a user-defined iterator type, which depends on requires-expression
// parameter binding for conjoined requires-expressions
// ([expr.prim.req.general]/2) being correct.

#include <compare>
#include <iterator>

// A hand-written random-access iterator, class type (like __normal_iterator).
struct It
{
  using value_type = int;
  using difference_type = long;
  using iterator_category = std::random_access_iterator_tag;

  int *p = nullptr;

  It() = default;
  It(const It &) = default;
  It &operator=(const It &) = default;

  int &operator*() const { return *p; }
  It &operator++() { ++p; return *this; }
  It operator++(int) { It t = *this; ++p; return t; }
  It &operator--() { --p; return *this; }
  It operator--(int) { It t = *this; --p; return t; }
  It &operator+=(difference_type n) { p += n; return *this; }
  It &operator-=(difference_type n) { p -= n; return *this; }
  It operator+(difference_type n) const { It t = *this; t += n; return t; }
  It operator-(difference_type n) const { It t = *this; t -= n; return t; }
  difference_type operator-(const It &o) const { return p - o.p; }
  int &operator[](difference_type n) const { return p[n]; }
  friend It operator+(difference_type n, const It &i) { return i + n; }
  bool operator==(const It &o) const { return p == o.p; }
  auto operator<=>(const It &o) const { return p <=> o.p; }
};

// A non-iterator: only dereferenceable, not incrementable.
struct NotIt
{
  int &operator*() const;
};

int main()
{
  // Positive: the full chain over the class iterator It.
  static_assert(std::input_or_output_iterator<It>, "It io");
  static_assert(std::input_iterator<It>, "It input");
  static_assert(std::forward_iterator<It>, "It forward");
  static_assert(std::bidirectional_iterator<It>, "It bidirectional");
  static_assert(std::random_access_iterator<It>, "It random_access");

  // Sanity: matches the pointer result.
  static_assert(std::random_access_iterator<int *>, "ptr random_access");

  // Negative: NotIt is not even an input_or_output_iterator.
  static_assert(!std::input_or_output_iterator<NotIt>, "NotIt not an iterator");

  return 0;
}
