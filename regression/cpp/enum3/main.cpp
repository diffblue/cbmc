enum MyEnum{ ZERO, ONE };

static_assert(MyEnum(ZERO)==ZERO, "enum constructor");
static_assert(MyEnum(0)==ZERO, "enum constructor");
static_assert(MyEnum()==ZERO, "enum constructor");

int main()
{
}
