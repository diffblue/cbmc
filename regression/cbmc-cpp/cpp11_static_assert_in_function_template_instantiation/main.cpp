// N5008 [dcl.pre]/13, [temp.inst]/11: a static_assert in the definition of
// a function template specialization that is instantiated (it is odr-used)
// is evaluated, and the program is ill-formed if it fails.  The front end
// reported "static assertion failed in a template instantiation ...
// (ignored)" as a warning and verified the program.  g++ 13 and clang++ 18
// reject it.
template <class T>
int size_of()
{
  static_assert(sizeof(T) == 1, "T must be one byte");
  return sizeof(T);
}
int main()
{
  return size_of<int>();
}
