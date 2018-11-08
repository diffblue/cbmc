[CPROVER Manual TOC](../../)

## Installation

### Requirements

CBMC is available for Windows, i86 Linux, and MacOS X. CBMC requires a
code pre-processing environment comprising of a suitable preprocessor
and an a set of header files.

1.  **Linux:** the preprocessor and the header files typically come with
    a package called *gcc*, which must be installed prior to the
    installation of CBMC.

2.  **Windows:** The Windows version of CBMC requires the preprocessor
    `cl.exe`, which is part of Microsoft Visual Studio. We recommend the
    free [Visual Studio Community
    2013](http://www.visualstudio.com/en-us/products/visual-studio-community-vs).

3.  **MacOS:** Install the [XCode Command Line
    Utilities](http://developer.apple.com/technologies/xcode.html) prior
    to installing CBMC. Just installing XCode alone is not enough.

Important note for Windows users: Visual Studio's `cl.exe` relies on a
complex set of environment variables to identify the target architecture
and the directories that contain the header files. You must run CBMC
from within the *Visual Studio Command Prompt*.

Note that the distribution files for the [Eclipse
plugin](http://www.cprover.org/eclipse-plugin/)
include the CBMC executable.  Therefore, if you intend to run CBMC
exclusively within Eclipse, you can skip the installation of the CBMC
executable.  However, you still have to install the compiler environment as
described above.

### Installing the CBMC Binaries

1.  Download CBMC for your operating system. The binaries are available
    from http://www.cprover.org/cbmc/.
2.  Unzip/untar the archive into a directory of your choice. We
    recommend to add this directory to your `PATH` environment variable.

You are now ready to use CBMC. We recommend you follow the
[tutorial](../cbmc/tutorial/).

### Building CBMC from Source

See the [CPROVER Developer
Documentation](http://cprover.diffblue.com/compilation-and-development.html).

## Installing the Eclipse Plugin

### Requirements

We provide a graphical user interface to CBMC which is
realized as a plugin to the Eclipse framework. Eclipse is available at
http://www.eclipse.org. We do not provide installation instructions for
Eclipse (basically, you only have to download the current version and
extract the files to your hard-disk) and assume that you have already
installed the current version.

Important note for Windows users: Visual Studio's `cl.exe` relies on a
complex set of environment variables to identify the target architecture
and the directories that contain the header files. You must run Eclipse
from within the *Visual Studio Command Prompt*.

### Installing the Eclipse Plugin

The installation instructions for the Eclipse Plugin, including the link
to the download site, are available
[here](http://www.cprover.org/eclipse-plugin/). This includes a small
tutorial on how to use the Eclipse plugin.

