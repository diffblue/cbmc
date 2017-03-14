public class test_float
{
   public static void main(/*String[] arg*/)
   {
      float inf = 100.0f / 0.0f;
      float minus_inf = -100.0f / 0.0f;
      float nan = 0.0f / 0.0f;
      String inf_string = Float.toString(inf);
      String mininf_string = Float.toString(minus_inf);
      String nan_string = Float.toString(nan);
      assert(nan_string.equals("NaN"));
      assert(inf_string.equals("Infinity"));
      assert(mininf_string.equals("-Infinity"));
   }
}
