# `x86-preprocessing': the test preprocesses for an x86 target (--winx64:
# gcc -m64), which GNU gcc for another architecture (aarch64) rejects
set(x86_preprocessing "")
if(NOT WIN32 AND NOT APPLE AND
   NOT CMAKE_SYSTEM_PROCESSOR MATCHES "^(x86_64|AMD64|amd64|i[3-6]86)$")
  set(x86_preprocessing -X x86-preprocessing)
endif()

if(NOT WIN32)
add_test_pl_tests(
    "$<TARGET_FILE:cbmc>" ${x86_preprocessing}
)
else()
add_test_pl_profile(
    "cbmc-library"
    "$<TARGET_FILE:cbmc>"
    "-C;-X;unix;-X;gcc-only"
    "CORE"
)
endif()
