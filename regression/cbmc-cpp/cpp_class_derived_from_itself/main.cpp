// [class.derived.general]/2: the base class shall not be an incompletely
// defined class -- X is incomplete in its own base-specifier-list
struct X : X
{
};
int main()
{
}
