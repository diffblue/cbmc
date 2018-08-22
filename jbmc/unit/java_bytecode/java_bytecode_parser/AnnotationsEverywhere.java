@interface ClassAnnotation {
}

@java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME)
@interface RuntimeClassAnnotation {
}

@interface FieldAnnotation {
}

@java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME)
@interface RuntimeFieldAnnotation {
}

@interface MethodAnnotation {
}

@java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME)
@interface RuntimeMethodAnnotation {
}

@interface ParameterAnnotation {
}

@java.lang.annotation.Retention(java.lang.annotation.RetentionPolicy.RUNTIME)
@interface RuntimeParameterAnnotation {
}

@ClassAnnotation
@RuntimeClassAnnotation
public class AnnotationsEverywhere {
    @FieldAnnotation
    @RuntimeFieldAnnotation
    public int x;

    @MethodAnnotation
    @RuntimeMethodAnnotation
    public void foo(
        @RuntimeParameterAnnotation int p,
        @ParameterAnnotation int q)
    {
    }
}
