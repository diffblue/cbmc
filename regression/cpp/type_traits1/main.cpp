#include <type_traits>

static_assert(!std::is_array<char>::value, "is_array<char>");
static_assert(std::is_array<char[]>::value, "is_array<char[]>");
static_assert(!std::is_array<char *>::value, "is_array<char *>");

static_assert(!std::is_class<char>::value, "is_class<char>");
static_assert(std::is_class<class some_class>::value, "is_class<class>");

enum some_enum { E1 };
static_assert(!std::is_enum<char>::value, "is_enum<char>");
static_assert(std::is_enum<some_enum>::value, "is_enum<some_enum>");
static_assert(!std::is_enum<int>::value, "is_enum<int>");

static_assert(std::is_floating_point<float>::value, "is_floating_point<float>");
static_assert(std::is_floating_point<double>::value, "is_floating_point<double>");
static_assert(!std::is_floating_point<some_enum>::value, "is_floating_point<some_enum>");

static_assert(!std::is_function<float>::value, "is_function<float>");
static_assert(std::is_function<void(void)>::value, "is_function<void(void)>");
static_assert(!std::is_function<void(*)(void)>::value, "is_function<void(*)(void)>");

static_assert(std::is_integral<char>::value, "is_integral<char>");
static_assert(std::is_integral<int>::value, "is_integral<int>");
static_assert(std::is_integral<bool>::value, "is_integral<bool>");
static_assert(!std::is_integral<float>::value, "is_integral<float>");
static_assert(!std::is_integral<double>::value, "is_integral<double>");

int main()
{
}
