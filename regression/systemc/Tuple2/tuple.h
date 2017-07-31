
#ifndef TUPLE_H
#define TUPLE_H

#define DECLARE_INSIDE

#ifndef NO_IO
#include <iostream>
#endif

// ---------------------------------------------------------------------
// Templates for passing & returning tuples

// null type
struct null_type {};

// a const value of null_type
inline const null_type cnull() {return null_type();}

#ifndef NO_IO
std::ostream& operator<<(std::ostream& os, const null_type dummy)
{
  os << "-";
  return os;
}
#endif

// a global to absorb "writes" to unused tuple fields.
// would be good to get rid of this.
null_type dummy;

template
   <class T0 = null_type,
    class T1 = null_type,
    class T2 = null_type,
    class T3 = null_type>
class ltuple;

template
   <class T0 = null_type,
    class T1 = null_type,
    class T2 = null_type,
    class T3 = null_type>
class tuple
{

  T0 el0;
  T1 el1;
  T2 el2;
  T3 el3;

public:

  friend tuple<T0,T1,T2,T3>
  ltuple<T0,T1,T2,T3>::operator= (tuple<T0,T1,T2,T3>);

#ifndef NO_IO
  std::ostream&
  dump (std::ostream& os) {
    os << "(" << el0 << "," << el1 << "," << el2 << "," << el3 << ")";
    return os;
  }
#endif

  tuple() {}

  tuple(T0 t0): el0(t0), el1(cnull()), el2(cnull()), el3(cnull()) {}

  tuple(T0 t0, T1 t1): el0(t0), el1(t1), el2(cnull()), el3(cnull()) {}

  tuple(T0 t0, T1 t1, T2 t2): el0(t0), el1(t1), el2(t2), el3(cnull()) {}

  tuple(T0 t0, T1 t1, T2 t2, T3 t3): el0(t0), el1(t1), el2(t2), el3(t3) {}

};

#ifndef NO_IO
template<class T0, class T1, class T2, class T3>
  std::ostream& operator<<(std::ostream& os, tuple<T0,T1,T2,T3> src)
{
  return src.dump(os);
}
#endif

template
   <class T0,
    class T1,
    class T2,
    class T3>
class ltuple
{

private:
  T0 &el0;
  T1 &el1;
  T2 &el2;
  T3 &el3;

public:

#ifdef DECLARE_INSIDE
  ltuple(T0 &t0, T1 &t1, T2 &t2, T3 &t3 )
    : el0(t0), el1(t1), el2(t2), el3(t3)
  {}

  tuple<T0,T1,T2,T3>
  operator= (tuple<T0,T1,T2,T3> src)
    {
      el0 = src.el0;
      el1 = src.el1;
      el2 = src.el2;
      el3 = src.el3;
      return src;
    }
#else
  ltuple(T0 &t0, T1 &t1, T2 &t2, T3 &t3 );

  tuple<T0,T1,T2,T3>
  operator= (tuple<T0,T1,T2,T3> src);
#endif
};


#ifndef DECLARE_INSIDE
template <class T0, class T1, class T2, class T3>
ltuple<T0,T1,T2,T3>::ltuple(T0 &t0, T1 &t1, T2 &t2, T3 &t3 )
  : el0(t0), el1(t1), el2(t2), el3(t3)
  {}

template <class T0, class T1, class T2, class T3>
tuple<T0,T1,T2,T3>
ltuple<T0,T1,T2,T3>::operator= (tuple<T0,T1,T2,T3> src)
{
  el0 = src.el0;
  el1 = src.el1;
  el2 = src.el2;
  el3 = src.el3;
  return src;
}
#endif

template <class T0>
ltuple<T0>
tie(T0 &t0)
{
  return ltuple<T0>(t0, dummy, dummy, dummy);
}

template <class T0, class T1>
ltuple<T0,T1>
tie(T0 &t0, T1 &t1)
{
  return ltuple<T0,T1>(t0,t1,dummy,dummy);
}

template <class T0, class T1, class T2>
ltuple<T0,T1,T2>
tie(T0 &t0, T1 &t1, T2 &t2)
{
  return ltuple<T0,T1,T2>(t0,t1,t2,dummy);
}

template <class T0, class T1, class T2, class T3>
ltuple<T0,T1,T2,T3>
tie(T0 &t0, T1 &t1, T2 &t2, T3 &t3)
{
  return ltuple<T0,T1,T2>(t0,t1,t2,t3);
}

#endif

