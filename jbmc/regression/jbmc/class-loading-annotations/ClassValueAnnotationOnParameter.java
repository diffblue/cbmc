public class ClassValueAnnotationOnParameter {
  public void classValueAnnotatedParameter(
    @AnnotationWithClassValue(MyClassA.class) int param) {}
}
