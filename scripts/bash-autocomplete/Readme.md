# CBMC Autocomplete Scripts for Bash
This directory contains an autocomplete script for bash.
## Installation
1. Compile cbmc and

2. `cd scripts/bash-autocomplete`

3.  `./extract-switches.sh`

4. Put the following at the end of you in your `~/.bashrc`, with the directories adapted to your directory structure:
    ```bash
    cbmcautocomplete=~/diffblue/cbmc/scripts/bash-autocomplete/cbmc.sh
    if [ -f $cbmcautocomplete ]; then
      . $cbmcautocomplete
    fi
    ```
## Usage
As with the usual autocomplete in bash, start typing a switch to complete it, for example:
```
cbmc --clas<TAB>
```
will complete to
```
cbmc --classpath
```

## Features implemented

* Completing all switches
* Completing values for `--cover`, `--mm` and `--arch`
* When completing a name of a file to analyze, only files with supported extensions are shown.
