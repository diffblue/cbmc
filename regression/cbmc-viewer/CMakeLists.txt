if(NOT WIN32)
    add_standalone_test(
        NAME cbmc-viewer
        COMMAND python3 "${CMAKE_CURRENT_SOURCE_DIR}/test.py"
    )
endif()

