#pragma once

template <typename T> class cow final {
public:
  cow() = default;

  template <typename... Ts>
  explicit cow(Ts &&... ts) : t_(new T(std::forward<Ts>(ts)...)) {
    t_->increment_use_count();
  }

  cow(const cow &rhs) {
    if (!rhs.t_->is_unshareable()) {
      t_ = rhs.t_;
      t_->increment_use_count();
    } else {
      t_ = new T(*t_);
    }
  }

  cow &operator=(const cow &rhs) {
    auto copy(rhs);
    swap(copy);
    return *this;
  }

  cow(cow &&rhs) { swap(rhs); }

  cow &operator=(cow &&rhs) {
    swap(rhs);
    return *this;
  }

  ~cow() {
    if (t_->is_unshareable()) {
      delete t_;
    } else {
      t_->decrement_use_count();
      if (t_->get_use_count() == 0) {
        delete t_;
      }
    }
  }

  void swap(cow &rhs) {
    using std::swap;
    swap(t_, rhs.t_);
  }

  const T &operator*() const { return *t_; }

  T &write(bool mark_unshareable) {
    if (!t_->is_unshareable() && t_->get_use_count() != 1) {

    } else {

    }
  }

private:
  T *t_ = nullptr;
};

class cow_base {
public:
  cow_base() = default;
  cow_base(const cow_base &) {}
  cow_base &operator=(const cow_base &) {}
  cow_base(cow_base &&) {}
  cow_base &operator=(cow_base &&) {}

  void increment_use_count() { use_count_ += 1; }
  void decrement_use_count() { use_count_ -= 1; }
  std::size_t get_use_count() const { return use_count_; }

  void set_unshareable(bool u) { use_count_ = u ? unshareable : 1; }
  bool is_unshareable() { return use_count_ == unshareable; }

protected:
  ~cow_base() = default;

private:
  static const std::size_t unshareable =
      std::numeric_limits<std::size_t>::max();
  std::size_t use_count_ = 0;
};
