// The orering of the following matters!

class FF
{
public:
  typedef int f;
};

// declare Z<>
template <typename T>
class Z;

// make an instance of Z<>
typedef Z<FF> my_Z;

// now define Z<>
template <typename T>
class Z
{
public:
  typename T::f some;
};

// trigger elaboration of Z<FF>
my_Z z;
