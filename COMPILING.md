# WHAT ARCHITECTURE?

CPROVER now needs a C++11 compliant compiler and works in the following
environments:

- Linux
- MacOS X
- Solaris 11
- FreeBSD 11
- Cygwin
- Microsoft Visual Studio

The rest of this document is split up into three parts: compilation on Linux,
MacOS, Windows.  Please read the section appropriate for your machine.

# COMPILATION ON LINUX

We assume that you have a Debian/Ubuntu or Red Hat-like distribution.

1. You need a C/C++ compiler, Flex and Bison, and GNU make.
   The GNU Make needs to be version 3.81 or higher.
   On Debian-like distributions, do as root:
   ```
   apt-get install g++ gcc flex bison make git libwww-perl patch
   ```
   On Red Hat/Fedora or derivates, do as root:
   ```
   dnf install gcc gcc-c++ flex bison perl-libwww-perl patch
   ```
   Note that you need g++ version 5.0 or newer.

   On Amazon Linux and similar distributions, do as root:
   ```
   yum install gcc72-c++ flex bison perl-libwww-perl patch
   ```

   To compile JBMC, you additionally need the JDK and Maven 3.
   On Debian-like distributions, do as root:
   ```
   apt-get install openjdk-8-jdk maven
   ```
   On Red Hat/Fedora or derivates, do as root:
   ```
   dnf install java-1.8.0-openjdk-devel maven
   ```

2. As a user, get the CBMC source via
   ```
   git clone https://github.com/diffblue/cbmc cbmc-git
   cd cbmc-git
   ```

3. To compile, do
   ```
   make -C src minisat2-download
   make -C src
   ```

4. Linking against an IPASIR SAT solver

   Get an IPASIR package and build picosat by default
   ```
   make -C src ipasir-build
   ```

   Build CBMC with IPASIR and link against the ipasir solver library
   Note: the LIBS variable could be pointed towards other solvers
   ```
   make -C src IPASIR=../../ipasir LIBS=$(pwd)/ipasir/libipasir.a
   ```

5. To compile JBMC, do
   ```
   make -C jbmc/src setup-submodules
   make -C jbmc/src
   ```

# COMPILATION ON SOLARIS 11

We assume Solaris 11.4 or newer.  To build JBMC, you'll need to install
Maven 3 manually.

1. As root, get the necessary development tools:
   ```
   pkg install gcc-c++-7 bison flex
   ```
2. As a user, get the CBMC source via
   ```
   git clone https://github.com/diffblue/cbmc cbmc-git
   cd cbmc-git
   ```
3. To compile CBMC, type
   ```
   gmake -C src minisat2-download DOWNLOADER=wget TAR=gtar
   gmake -C src
   ```
4. To compile JBMC, type
   ```
   gmake -C jbmc/src setup-submodules
   gmake -C jbmc/src
   ```

# COMPILATION ON FREEBSD 11

1. As root, get the necessary tools:
   ```
   pkg install bash gmake git www/p5-libwww patch flex bison
   ```
   To compile JBMC, additionally install
   ```
   pkg install openjdk8 wget maven3
   ```
2. As a user, get the CBMC source via
   ```
   git clone https://github.com/diffblue/cbmc cbmc-git
   cd cbmc-git
   ```
3. To compile CBMC, do
   ```
   gmake -C src minisat2-download
   gmake -C src
   ```
4. To compile JBMC, do
   ```
   gmake -C jbmc/src setup-submodules
   gmake -C jbmc/src
   ```

# COMPILATION ON MACOS X

Follow these instructions:

1. You need a C/C++ compiler, Flex and Bison, and GNU make. To this end, first
   install the XCode from the App-store and then type
   ```
   xcode-select --install
   ```
   in a terminal window.
2. Then get the CBMC source via
   ```
   git clone https://github.com/diffblue/cbmc cbmc-git
   cd cbmc-git
   ```
3. To compile CBMC, do
   ```
   make -C src minisat2-download
   make -C src
   ```
4. To compile JBMC, you additionally need Maven 3, which has to be installed
   manually. Then do
   ```
   make -C jbmc/src setup-submodules
   make -C jbmc/src
   ```

# COMPILATION ON WINDOWS

There are two options: the Visual Studio compiler with version 12 (2013) or
later, or the MinGW cross compiler with version 5.4 or later.
We recommend Visual Studio.

Follow these instructions:

1. First install Cygwin, then from the Cygwin setup facility install the
   following packages: `flex, bison, tar, gzip, git, make, wget, patch,
   libwww-perl`.
2. Get the CBMC source via
   ```
   git clone https://github.com/diffblue/cbmc cbmc-git
   cd cbmc-git
   ```
3. Depending on your choice of compiler:
   1. To compile with Visual Studio, change the second line of `src/config.inc`
      to
      ```
      BUILD_ENV = MSVC
      ```
      Open the Developer Command Prompt for Visual Studio, then start the
      Cygwin shell with
      ```
      bash.exe -login
      ```
   2. To compile with MinGW, use Cygwin setup to install a mingw g++ compiler
      package, i.e. one of `mingw{32,64}-{x86_64,i686}-gcc-g++`. You may also
      have to adjust the section in `src/common` that defines `CC` and `CXX`
      for BUILD_ENV = Cygwin.
      Then start the Cygwin shell.
4. To compile CMBC, open the Cygwin shell and type
   ```
   make -C src DOWNLOADER=wget minisat2-download
   make -C src
   ```
5. To compile JBMC, you additionally need the JDK and Maven 3, which have
   to be installed manually. Then open the Cygwin shell and type
   ```
   make -C jbmc/src setup-submodules
   make -C jbmc/src
   ```

(Optional) A Visual Studio project file can be generated with the script
"generate_vcxproj" that is in the subdirectory "scripts".  The project file is
helpful for GUI-based tasks, e.g., the class viewer, debugging, etc., and can
be used for building with MSBuild.  Note that you still need to run flex/bison
using "make generated_files" before opening the project.

# WORKING WITH CMAKE

There is also a build based on CMake instead of hand-written
makefiles. It should work on a wider variety of systems than the standard
makefile build, and can integrate better with IDEs and static-analysis tools.
On Windows, the CMake build does not depend on Cygwin or MinGW, and doesn't
require manual modification of build files.

1. Ensure you have all the build dependencies installed. Build dependencies are
   the same as for the makefile build, but with the addition of CMake version
   3.2 or higher. The installed CMake version can be queried with `cmake
   --version`. To install cmake:
   - On Debian-like distributions, do
     ```
     apt-get install cmake
     ```
   - On Red Hat/Fedora or derivates, do
     ```
     dnf install cmake
     ```
   - On macOS, do
     ```
     xcode-select --install
     ```
     You shoud also install [Homebrew](https://brew.sh), after which you can
     run `brew install cmake` to install CMake.
   - On Windows, ensure you have Visual Studio 2013 or later installed.
     Then, download CMake from the [official download
     page](https://cmake.org/download).
     You'll also need `git` and `patch`, which are both provided by the
     [git for Windows](git-scm.com/download/win) package.
     Finally, Windows builds of flex and bison should be installed from
     [the sourceforge page](sourceforge.net/projects/winflexbison).
     The easiest way to 'install' these executables is to unzip them and to
     drop the entire unzipped package into the CBMC source directory.
   - Use of CMake has not been tested on Solaris or FreeBSD. However, it should
     be possible to install CMake from the system package manager or the
     [official download page](https://cmake.org/download) on those systems.
     The dependencies (as listed in the relevant sections above) will also be
     required, and should be installed using the suggested methods.
2. Navigate to the *top level* folder of the project. This is different from
   the Makefile build, which requires you to navigate to the `src` directory
   first.
3. Update git submodules:
   ```
   git submodule update --init
   ```
4. Generate build files with CMake:
   ```
   cmake -H. -Bbuild
   ```
   This command tells CMake to use the configuration in the current directory,
   and to generate build files into the `build` directory.  This is the point
   to specify custom build settings, such as compilers and build back-ends. You
   can use clang (for example) by adding the argument
   `-DCMAKE_CXX_COMPILER=clang++` to the command line. You can also tell CMake
   to generate IDE projects by supplying the `-G` flag.  Run `cmake -G` for a
   comprehensive list of supported back-ends.

   Generally it is not necessary to manually specify individual compiler or
   linker flags, as CMake defines a number of "build modes" including Debug and
   Release modes. To build in a particular mode, add the flag
   `-DCMAKE_BUILD_TYPE=Debug` (or `Release`) to the initial invocation.

   If you *do* need to manually add flags, use `-DCMAKE_CXX_FLAGS=...` and
   `-DCMAKE_EXE_LINKER_FLAGS=...`. This is useful for enabling clang's
   sanitizers.

   Finally, to enable building universal binaries on macOS, you can pass the
   flag `-DCMAKE_OSX_ARCHITECTURES=i386;x86_64`. If you don't supply this flag,
   the build will just be for the architecture of your machine.
5. Run the build:
   ```
   cmake --build build
   ```
   This command tells CMake to invoke the correct tool to run the build in the
   `build` directory. You can also use the build back-end directly by invoking
   `make`, `ninja`, or opening the generated IDE project as appropriate.

# WORKING WITH ECLIPSE

To work with Eclipse, do the following:

1. Select File -> New -> Makefile Project with Existing Code
2. Type "cprover" as "Project Name"
3. Select the "src" subdirectory as "Existing Code Location"
4. Select a toolchain appropriate for your platform
5. Click "Finish"
6. Select Project -> Build All

