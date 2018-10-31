public class ArrayValueAnnotationOnParameter {
  public void classValueAnnotatedParameter(
      @AnnotationWithArrayValue({MyClassA.class, MyClassB.class}) int param) {}
}
