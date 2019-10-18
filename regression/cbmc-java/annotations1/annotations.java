@interface ClassAnnotation {}

@interface MethodAnnotation {}

@ClassAnnotation
class annotations {
  @MethodAnnotation
  void test() {}
}
