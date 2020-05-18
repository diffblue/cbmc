REM Patch cbmc for Visual Studio

REM Set up PATH to find Git Bash shell tools
PATH=%PATH%;"c:\Program Files\Git\usr\bin"

REM Patch CBMC with Visual Studio patches
patch -p1 < .github\workflows\vs2019\cbmc.patch

