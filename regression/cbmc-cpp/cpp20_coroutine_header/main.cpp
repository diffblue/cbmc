#if !defined(_MSC_VER) && __has_include(<coroutine>)
// C++20: <coroutine> header parsing
#  include <coroutine>
int main()
{
}

#else
int main()
{
}
#endif
