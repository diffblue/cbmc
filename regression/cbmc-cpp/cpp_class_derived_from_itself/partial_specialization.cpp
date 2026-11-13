// [class.derived.general]/2: P<int &>, an instance of the partial
// specialization, is incomplete in its own base-specifier-list
template <class T>
struct P;
template <class T>
struct P<T &> : P<T &>
{
};
int main()
{
  P<int &> p;
}
