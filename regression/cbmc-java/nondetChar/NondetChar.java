import org.cprover.CProver;

class NondetChar
{
    static void foo()
    {
        char x = CProver.nondetChar();
        assert x == '\0';
    }
}
