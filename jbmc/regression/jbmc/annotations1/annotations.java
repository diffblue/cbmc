@interface ClassAnnotation {
}

@interface MethodAnnotation {
}

@interface FieldAnnotation {
}

@ClassAnnotation
public class annotations
{
    @FieldAnnotation
    public int x;

    @FieldAnnotation
    public static int y;

    @MethodAnnotation
    public void main()
    {
    }
}
