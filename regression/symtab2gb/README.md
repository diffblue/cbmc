This directory contains tests based on converting json symtab files to goto
binaries using the symtab2gb binary and then passing the generated goto binary
to cbmc. Additional arguments specified in the `.desc` file up until a possible
`_` will be passed to the symtab2gb binary, any arguments specified after an `_`
are passed to cbmc.
