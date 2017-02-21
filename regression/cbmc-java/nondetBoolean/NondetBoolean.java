import org.cprover.CProver;

class NondetBoolean
{
    static void foo()
    {
        boolean x = CProver.nondetBoolean();
        assert x == false;
    }
}
