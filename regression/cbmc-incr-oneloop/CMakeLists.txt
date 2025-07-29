add_test_pl_tests(
    "perl ../timeout.pl 25 $<TARGET_FILE:cbmc> --slice-formula"
)
