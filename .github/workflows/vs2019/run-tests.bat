@REM Run tests on visual studio 2019 generated build

@echo "Set up PATH to find Visual Studio tools"
call "C:\Program Files (x86)\Microsoft Visual Studio\2019\Enterprise\VC\Auxiliary\Build\vcvars64.bat"

@echo PATH:
@echo
@echo %PATH%

@echo Run tests with ctest
cd build
ctest -j2 -V -L CORE -C Release .
