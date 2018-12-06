[CPROVER Manual TOC](../)

## Integration into Visual Studio

Visual Studio version 2008 onwards comes with a new XML-based build
system called
[MSBuild](http://msdn.microsoft.com/en-us/library/ms171452.aspx).
The MSBuild system is also activated when triggering a build from the
Visual Studio GUI. The project files created by the Visual Studio GUI
are used as input by the MSBuild tool.

To use MSBuild to generate goto-binaries from your
Visual Studio project:

1.  Install the `goto-cl.exe` and `goto-link.exe` binaries in some
    directory that is contained in the PATH environment variable.

2.  Add a configuration for the goto-cc build for your project in the
    configuration manager, named "goto-cc".

3.  Open the Visual Studio Command Prompt (in the Tools menu).

4.  Locate the directory that contains the project. Change into this
    directory.

5.  Type

        msbuild /p:CLToolExe=goto-cl.exe /p:LinkToolExe=goto-link.exe    /p:Flavor=goto-cc /p:Platform=x86

    You can adjust the platform as required. The "Flavor" given should
    match the configuration you created earlier.

Note that the recent versions of goto-cc also support file names with
non-ASCII (Unicode) characters on Windows platforms.
