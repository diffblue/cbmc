#ifdef __GNUC__
using type __attribute__((__nodebug__)) = int;

typedef int my_int_t;
namespace N
{
using ::my_int_t __attribute__((__using_if_exists__));
}
#endif

int main(int argc, char *argv[])
{
}
