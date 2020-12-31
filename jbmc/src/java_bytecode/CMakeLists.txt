# target 'java_bytecode' depends on all .cpp and .h files
file(GLOB sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
add_library(java_bytecode ${sources} ${headers})

# define the include directories (passed to the compiler with -I) that those
# targets wishing to depend on the target 'java_bytecode' may want to use
generic_includes(java_bytecode)

# if you link java_bytecode.a in, then you also need to link other .a libraries
# in
target_link_libraries(java_bytecode util goto-programs miniz json ansi-c)
