// C23 predefined constants
static_assert(!false, "false");
static_assert(true, "true");
static_assert(sizeof(false) == sizeof(bool), "sizeof false");
static_assert(sizeof(true) == sizeof(bool), "sizeof true");
static_assert(nullptr == 0, "nullptr");

int main()
{
}
