#pragma clang attribute _LibcxxExplicitABIAnnotations.push
namespace std {
   namespace {
  template < int __v > struct integral_constant {
    static const int value = __v;
  };
  void declval() { ; }
  template < bool > struct _IfImpl
    ;
  
  template < bool _Cond, class , class  >
  using _If = _IfImpl< _Cond >;
  template < int _Bp, class _ElseRes > struct conditional {
    using type = _If< _Bp, int, _ElseRes >;
  };
  template < bool _Bp, class _If, class _Then >
  using __conditional_t = conditional< _Bp, _Then >::type;
  template < class > struct allocator ;
  template < class _Tp, class =  _Tp  > class vector;
  struct allocator_traits {
    using size_type = decltype(sizeof(int));
  };
  template < class , class , class >
  struct __split_buffer_pointer_layout {
  void
    __set_sentinel() ;
  };
  template < template < class, class, class > class _Layout >
  struct __split_buffer {
    using __base_type = _Layout< __split_buffer, int, int >;
    using __base_type::__set_sentinel;

  struct _ConstructTransaction {
      _ConstructTransaction() {
        __parent_->__set_sentinel();
      }

    __split_buffer *__parent_;
    };
  };
  struct __vector_layout {
    using _SplitBuffer = __split_buffer< __split_buffer_pointer_layout >;
  };
  template < class _Tp, class > struct vector {
  using __alloc_traits = allocator_traits;
    using __trivially_relocatable = __conditional_t<
        integral_constant< __is_trivially_copyable(int) >::value,
        vector, void >;
    __alloc_traits::size_type
    size() ;
    void
    push_back(int );
  };
  } } // std
#pragma clang attribute _LibcxxExplicitABIAnnotations.pop
extern void __CPROVER_assert(bool, char *);
int main() {
  std::vector< int > v;
  v.push_back(7);
  __CPROVER_assert(v.size() == 1, "size after one push_back");
}
