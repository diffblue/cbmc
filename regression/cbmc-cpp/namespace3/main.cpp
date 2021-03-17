#include <cassert>
namespace std
{
struct A
{
  int i;
};
} // namespace std

std::A a;

int main(int argc, char *argv[])
{
  assert(a.i == 0);
}
