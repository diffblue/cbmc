@REM Install bison and flex

echo "Set up PATH to find Git Bash shell tools"
PATH=%PATH%;"c:\Program Files\Git\usr\bin"

echo "Download bison and flex"
curl -L https://downloads.sourceforge.net/project/winflexbison/win_flex_bison-latest.zip > bison.zip

echo "Intall bison and flex"
unzip bison.zip

