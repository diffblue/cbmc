file(GLOB_RECURSE sources "*.cpp")
add_library(cpp ${sources}) 

generic_includes(cpp)

target_link_libraries(cpp util ansi-c)
