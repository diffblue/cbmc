@REM Build installer

echo on

@REM PGK can have values cbmc or cbmc-latest
set PKG=%1
set SCRIPTDIR=.github\workflows\vs2019

if not "%PKG%"=="cbmc" if not "%PKG%"=="cbmc-latest" (
  echo PKG must be "cbmc" or "cbmc-latest", found "%PKG%"
  exit 1
)

echo "Set up PATH to find wix"
PATH=%PATH%;"C:\Program Files (x86)\WiX Toolset v3.11\bin"

echo "Build installer: run candle"
candle -o %PKG%.wixobj -arch x64 %SCRIPTDIR%\%PKG%.wxs

echo "Build installer: run light"
light -o %PKG%.msi -ext WixUIExtension %PKG%.wixobj

echo %cd%
dir %cd%
