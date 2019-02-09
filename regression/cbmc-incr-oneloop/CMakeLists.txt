add_test_pl_tests(
    "perl -e 'alarm shift @ARGV; exec @ARGV' 8 $<TARGET_FILE:cbmc> --slice-formula"
)
