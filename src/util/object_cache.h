#ifndef CPROVER_GOTO_PROGRAMS_OBJECT_CACHE_H
#define CPROVER_GOTO_PROGRAMS_OBJECT_CACHE_H

#include <map>
#include <memory>

typedef void (*class_idt)();

// This generates a static method for each template instantiation whose address
// can be used as a unique key. We would use typeid(T) as such a key, but cbmc
// may be built without RTTI.
template <typename T>
struct cached_type_idt
{
  static void id()
  {
  }
};

/// A cache of persistent objects.
/// There can only be one instance of each type in the cache at a time.
class object_cachet
{
public:
  /// Retrives the current instance of the templated type if it exists in the cache,
  /// creates it with the passed-in arguments and returns if not.
  template <typename cached_type, typename... arguments>
  cached_type &get_or_create(arguments &&... values)
  {
    // We're key'd off the current templates type.
    const class_idt current_type_id = &cached_type_idt<cached_type>::id;
    auto container_iterator = cache_map.find(current_type_id);
    if(container_iterator == cache_map.end())
    {
      // This creates a new instance of the object we're caching, stores it in
      // a container object in our map, then returns an iterator pointing at
      // that element.
      container_iterator =
        cache_map
          .emplace(
            current_type_id,
            std::unique_ptr<base_cache_containert>(
              new cache_containert<cached_type>(
                cached_type(std::forward<arguments>(values)...))))
          .first;
    }

    return **static_cast<cache_containert<cached_type> *>(
      container_iterator->second.get());
  }

  /// Erases the instance of the templated type from our cache.
  template <typename cached_type>
  void erase()
  {
    const class_idt current_type_id = &cached_type_idt<cached_type>::id;
    cache_map.erase(current_type_id);
  }

  /// Clears the internal cache of all stored types.
  void clear()
  {
    cache_map.clear();
  }

private:
  /// Non-templated container base so we can have a map full of various
  /// template instantiations.
  class base_cache_containert
  {
  public:
    virtual ~base_cache_containert() = default;
  };

  /// Templated container for persistent storage of heavy-to-create objects.
  template <typename T>
  class cache_containert : public base_cache_containert
  {
  private:
    T cached_value;

  public:
    explicit cache_containert(T stored_value)
      : cached_value(std::move(stored_value))
    {
    }

    T &operator*()
    {
      return cached_value;
    }
  };

  std::map<class_idt, std::unique_ptr<base_cache_containert>> cache_map;
};

#endif //CPROVER_GOTO_PROGRAMS_OBJECT_CACHE_H
