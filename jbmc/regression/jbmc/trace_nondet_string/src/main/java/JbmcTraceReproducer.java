public final class JbmcTraceReproducer
{
  public static void verify()
  {
    final String name = JbmcTraceReproducer.class.getName();
    assert name.length() < 4_194_304;
  }
}
