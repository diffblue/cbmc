add_test_pl_tests(
    "perl ../timeout.pl 8 $<TARGET_FILE:cbmc> --slice-formula"
)
