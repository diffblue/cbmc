// C++11 allows = delete on non-member functions.

void deleted_function() = delete;

namespace ns
{
void another_deleted() = delete;
}

int main()
{
  return 0;
}
