public class RegionMatches
{
    public static void constant(int in)
    {
        String s3 = "Automatic Test Generation";
        String s4 = "automatic test generation";
        String s4 = "automatic test generationn";

        // test regionMatches (case sensitive)
        if (in == 0)
            assert s3.regionMatches(0, s3, 0, 5); // should succeed
        else if (in == 1)
            assert !s3.regionMatches(0, s4, 0, 5); // should fail
        else if (in == 2)
            assert s3.regionMatches(true, 0, s4, 0, 5); // should succeed (ignore case)
        else if (in == 3)
            assert s3.regionMatches(true, 0, s5, 0, 5); // should fail (ignore case)
    }
}
