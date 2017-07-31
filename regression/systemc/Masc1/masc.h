#ifndef MASC_H
#define MASC_H

typedef unsigned uint;

// ---------------------------------------------------------------------
// Templates for passing & returning tuples and arrays

template <class T1, class T2, class T3 = bool, class T4 = bool>
class mv {
    T1 first;
    T2 second;
    T3 third;
    T4 fourth;
  public:
    mv(T1 x, T2 y) {first = x; second = y;}
    mv(T1 x, T2 y, T3 z) {first = x; second = y; third = z;}
    mv(T1 x, T2 y, T3 z, T4 w) {first = x; second = y; third = z; fourth = w;}
    void assign(T1 &x, T2 &y) {x = first; y = second;}
    void assign(T1 &x, T2 &y, T3 &z) {x = first; y = second; z = third;}
    void assign(T1 &x, T2 &y, T3 &z, T4 &w) {x = first; y = second; z = third; w = fourth;}
};

template <uint m, class T>
class array {
  public:
    T elt[m];
};


// Assert is sometimes a macro, which screws up our translation.
// If we are using the MASC translator we want to prevent its expansion.
#ifdef __MASC__
#undef assert
#endif

#endif

