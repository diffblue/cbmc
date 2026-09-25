# Unit proofs: CBMC applied to its own code base with nondeterministic
# inputs (see README.md).  Only CORE entries run by default; KNOWNBUG
# entries track the front-end defect or scaling limit that blocks them.
add_test_pl_tests(
    "$<TARGET_FILE:cbmc>"
)
set_tests_properties("unit-proofs-CORE" PROPERTIES TIMEOUT 900)
