import org.cprover.OverlayClassImplementation;
import org.cprover.OverlayMethodImplementation;

@OverlayClassImplementation
public class Test
{
  public int x;

  @OverlayMethodImplementation
  public static void main(String[] args)
  {
    assert(true);
  }
}
