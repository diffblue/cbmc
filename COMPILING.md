# WHAT ARCHITECTURE?

CPROVER now needs a C++11 compliant compiler and works in the following
environments:

- Linux
- MacOS X
- Solaris 11
- FreeBSD 11
- Cygwin (We recommend the i686-pc-mingw32-g++ cross compiler, version 5.4 or
  above.)
- Microsoft's Visual Studio version 12 (2013), version 14 (2015), or version 15
  (older versions won't work)

The rest of this document is split up into three parts: compilation on Linux,
MacOS, Windows.  Please read the section appropriate for your machine.

# COMPILATION ON LINUX

We assume that you have a Debian/Ubuntu or Red Hat-like distribution.

1. You need a C/C++ compiler, Flex and Bison, and GNU make.
   The GNU Make needs to be version 3.81 or higher.
   On Debian-like distributions, do
   ```
   apt-get install g++ gcc flex bison make git libwww-perl patch
   ```
   On Red Hat/Fedora or derivates, do
   ```
   yum install gcc gcc-c++ flex bison perl-libwww-perl patch devtoolset-6
   ```
   Note that you need g++ version 4.9 or newer.
2. As a user, get the CBMC source via
   ```
   git clone https://github.com/diffblue/cbmc cbmc-git
   ```
3. On Debian or Ubuntu, do
   ```
   cd cbmc-git/src
   make minisat2-download
   make
   ```
   On Redhat/Fedora etc., do
   ```
   cd cbmc-git/src
   make minisat2-download
   scl enable devtoolset-6 bash
   make
   ```

# COMPILATION ON SOLARIS 11

1. As root, get the necessary development tools:
   ```
   pkg install system/header developer/lexer/flex developer/parser/bison developer/versioning/git
   pkg install --accept developer/gcc/gcc-c++-5
   ```
2. As a user, get the CBMC source via
   ```
   git clone https://github.com/diffblue/cbmc cbmc-git
   ```
3. Get MiniSat2 by entering
   ```
   cd cbmc-git
   wget http://ftp.debian.org/debian/pool/main/m/minisat2/minisat2_2.2.1.orig.tar.gz
   gtar xfz minisat_2.2.1.orig.tar.gz
   mv minisat2-2.2.1 minisat-2.2.1
   (cd minisat-2.2.1; patch -p1 < ../scripts/minisat-2.2.1-patch)
   ```
4. Type
   ```
   cd src; gmake
   ```
   That should do it. To run, you will need
   ```
   export LD_LIBRARY_PATH=/usr/gcc/4.9/lib
   ```

# COMPILATION ON FREEBSD 11

1. As root, get the necessary tools:
   ```
   pkg install bash gmake git www/p5-libwww patch flex bison
   ```
2. As a user, get the CBMC source via
   ```
   git clone https://github.com/diffblue/cbmc cbmc-git
   ```
3. Do
   ```
   cd cbmc-git/src
   ```
4. Do
   ```
   gmake minisat2-download
   gmake
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
   ```
3. Then type
   ```
   cd cbmc-git/src
   make minisat2-download
   make
   ```

# COMPILATION ON WINDOWS

There are two options: compilation using g++ from Cygwin, or using Visual
Studio's compiler. As Cygwin has significant overhead during process creation,
we advise you use Visual Studio.

Follow these instructions:

1. You need a C/C++ compiler, Flex and Bison, GNU tar, gzip2, GNU make, and
   patch. The GNU Make needs to be version 3.81 or higher.  If you don't
   already have the above, we recommend you install Cygwin.
2. You need a SAT solver (in source). We recommend MiniSat2. Using a
   browser, download from
   ```
   http://ftp.debian.org/debian/pool/main/m/minisat2/minisat2_2.2.1.orig.tar.gz
   ```
   and then unpack with
   ```
   tar xfz minisat-2.2.1.tar.gz
   mv minisat minisat-2.2.1
   cd minisat-2.2.1
   patch -p1 < ../scripts/minisat-2.2.1-patch
   ```
   The patch removes the dependency on zlib and prevents a problem with a
   header file that is often unavailable on Windows.
   1. To compile with Cygwin, install the mingw compilers, and adjust
      the second line of config.inc to say
      ```
      BUILD_ENV = MinGW
      ```
   2. To compile with Visual Studio, make sure you have at least Visual
      Studio version 12 (2013), and adjust the second line of config.inc to say
      ```
      BUILD_ENV = MSVC
      ```
      Open the Visual Studio Command prompt, and then bash.exe -login from
      Cygwin from in there.
3. Type cd src; make - that should do it.

(Optional) A Visual Studio project file can be generated with the script
"generate_vcxproj" that is in the subdirectory "scripts".  The project file is
helpful for GUI-based tasks, e.g., the class viewer, debugging, etc., and can
be used for building with MSBuild.  Note that you still need to run flex/bison
using "make generated_files" before opening the project.

# WORKING WITH CMAKE (EXPERIMENTAL)

There is an experimental build based on CMake instead of hand-written
makefiles. It should work on a wider variety of systems than the standard
makefile build, and can integrate better with IDEs and static-analysis tools.

1. Run `cmake --version`. If you get a command-not-found error, or the
   installed version is lower than 3.2, go and install a new version. Most
   Linux distributions have a package for CMake, and Mac users can get it
   through Homebrew.  Windows users should download it manually from cmake.org.
2. Create a directory to store your build:
   ```
   mkdir build
   ```
   Run this from the *top level* folder of the project. This is different from
   the other builds, which require you to `cd src` first.
3. Generate build files with CMake:
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
4. Run the build:
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

# CODE COVERAGE

Code coverage metrics are provided using gcov and lcov. Ensure that you have
installed lcov from http://ltp.sourceforge.net/coverage/lcov.php note for
ubuntu lcov is available in the standard apt-get repos.

To get coverage metrics run the following script from the regression directory:
```
get_coverage.sh
```
This will:
 1) Rebuild CBMC with gcov enabled
 2) Run all the regression tests
 3) Collate the coverage metrics
 4) Provide an HTML report of the current coverage

# USING CLANG-FORMAT

CBMC uses clang-format to ensure that the formatting of new patches is readable
and consistent. There are two main ways of running clang-format: remotely, and
locally.

## RUNNING CLANG-FORMAT REMOTELY

When patches are submitted to CBMC, they are automatically run through
continuous integration (CI). One of the CI checks will run clang-format over
the diff that your pull request introduces. If clang-format finds formatting
issues at this point, the build will be failed, and a patch will be produced
in the CI output that you can apply to your code so that it conforms to the
style guidelines.

To apply the patch, copy and paste it into a local file (`patch.txt`) and then
run:
```
patch -p1 -i patch.txt
```
Now, you can commit and push the formatting fixes.

## RUNNING CLANG-FORMAT LOCALLY

### INSTALLATION

To avoid waiting until you've made a PR to find formatting issues, you can
install clang-format locally and run it against your code as you are working.

Different versions of clang-format have slightly different behaviors. CBMC uses
clang-format-3.8 as it is available the repositories for Ubuntu 16.04 and
Homebrew.
To install on a Unix-like system, try installing using the system package
manager:
```
apt-get install clang-format-3.8  # Run this on Ubuntu, Debian etc.
brew install clang-format@3.8     # Run this on a Mac with Homebrew installed
```

If your platform doesn't have a package for clang-format, you can download a
pre-built binary, or compile clang-format yourself using the appropriate files
from the [LLVM Downloads page](http://releases.llvm.org/download.html).

An installer for Windows (along with a Visual Studio plugin) can be found at
the [LLVM Snapshot Builds page](http://llvm.org/builds/).

### FORMATTING A RANGE OF COMMITS

Clang-format is distributed with a driver script called git-clang-format-3.8.
This script can be used to format git diffs (rather than entire files).

After committing some code, it is recommended to run:
```
git-clang-format-3.8 upstream/develop
```
*Important:* If your branch is based on a branch other than `upstream/develop`,
use the name or checksum of that branch instead. It is strongly recommended to
rebase your work onto the tip of the branch it's based on before running
`git-clang-format` in this way.

### RETROACTIVELY FORMATTING INDIVIDUAL COMMITS

If your works spans several commits and you'd like to keep the formatting
correct in each individual commit, you can automatically rewrite the commits
with correct formatting.

The following command will stop at each commit in the range and run
clang-format on the diff at that point.  This rewrites git history, so it's
*unsafe*, and you should back up your branch before running this command:
```
git filter-branch --tree-filter 'git-clang-format-3.8 upstream/develop' \
  -- upstream/develop..HEAD
```
*Important*: `upstream/develop` should be changed in *both* places in the
command above if your work is based on a different branch. It is strongly
recommended to rebase your work onto the tip of the branch it's based on before
running `git-clang-format` in this way.
