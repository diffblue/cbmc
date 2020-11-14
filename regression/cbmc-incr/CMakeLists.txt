add_test_pl_tests(
    "perl ../timeout.pl 30 $<TARGET_FILE:cbmc> --incremental --magic-numbers"
)
