@REM Build CBMC with Visual Studio 2019

echo "Set up PATH to find Visual Studio tools"
call "C:\Program Files (x86)\Microsoft Visual Studio\2019\Enterprise\VC\Auxiliary\Build\vcvars64.bat"

echo "Set up PATH to find Git Bash shell tools and bison/flex"
PATH=%PATH%;"c:\Program Files\Git\usr\bin";%cd%

echo "Remove chocolatey"
del /s /q "C:\ProgramData\Chocolatey\bin"

echo "Remove cmake"
del /s /q "C:\Program Files\CMake\bin"

echo "Remove strawberry"
del /s /q "c:/Strawberry/c/bin"

echo "Configure CBMC with cmake"
cmake -S. -Bbuild -GNinja

echo "Build CBMC with cmake"
cmake --build build
