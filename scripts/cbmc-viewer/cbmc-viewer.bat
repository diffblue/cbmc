@echo off

REM Run cbmc-viewer from the Windows command prompt.

SET dir=%~dp0
python %dir%cbmc-viewer %*
