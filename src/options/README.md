This module is for options data structures. The header files are packaged with
the libcprover-cpp library without headers for the rest of the repository,
such as those from /src/util. Because of this these public headers must not
include repository internal/private headers as these will be unavailable to
library consumers.

This module is designed to have link dependencies only on the C++ standard
libraries. This is intended to break potential cyclic linking dependencies
between code modules which write the options and code modules which read or are
configured based on the options.
