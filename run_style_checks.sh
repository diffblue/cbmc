CPPLINT="python scripts/cpplint.py --filter=-whitespace/operators,-readability/identifier_spacing"
CLANG_CMD="clang-format"
GOTO_INST_SRC="src/goto-instrument/"
# UTIL_SRC="src/util/"
FILES=(
    "rra.cpp"
    "rra.h"
    "rra_spec.cpp"
    "rra_spec.h"
    "rra_spec_gen.cpp"
    "rra_spec_gen.h"
)
# OTHER_FILES=(
#     "file_util.cpp"
#     "file_util.h"
# )

# cpplint checks

for file in "${FILES[@]}"; do
    $CPPLINT $GOTO_INST_SRC$file 2>&1
done

# for file in "${OTHER_FILES[@]}"; do
#     $CPPLINT $UTIL_SRC$file 2>&1
# done

# clang-format checks
for file in "${FILES[@]}"; do
    FMT_FILE=${file}".fmt"
    $CLANG_CMD $GOTO_INST_SRC$file > $FMT_FILE
    echo "clang-format output for ${file}"
    diff $GOTO_INST_SRC$file $FMT_FILE
done

# for file in "${OTHER_FILES[@]}"; do
#     FMT_FILE=${file}".fmt"
#     $CLANG_CMD $UTIL_SRC$file > $FMT_FILE
#     echo "clang-format output for ${file}"
#     diff $UTIL_SRC$file $FMT_FILE
# done
