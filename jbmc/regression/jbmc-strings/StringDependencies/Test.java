class Test {
    void test(String s) {
        // Filter
        if(s == null)
            return;

        // Act

        // this matters for the final test
        String t = s.concat("_foo");

        // these should be ignored by the solver as they
        // do not matter for the final test
        String u = s.concat("_bar");
        String v = s.concat("_baz");
        String w = s.concat("_fiz");
        String x = s.concat("_buz");

        // Assert
        assert t.endsWith("foo");
    }
}
