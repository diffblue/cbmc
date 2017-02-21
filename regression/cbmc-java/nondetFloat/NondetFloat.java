import org.cprover.CProver;

class NondetFloat
{
    static void foo()
    {
        float x = CProver.nondetFloat();
        assert x == 0;
    }
}
