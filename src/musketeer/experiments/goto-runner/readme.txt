
Debian experiments
==================

The Debian experiments can be run with the script goto-runner.sh. The script
runs a goto binary analysis tool on the goto binaries contained in archives held
at a certain URL.

The script reads a configuration file <hostname>.config, with <hostname> being
the hostname of the machine the script is run on (as can be retrieved by the
command 'hostname'). Various options can be configured in this file, such as the
URL from which to download packages, the tools to use, or the analysis timeout.
For an example configuration file see dkr11.cs.ox.ac.uk.config.

The output of successful runs is put into a directory 'success', and the output
of erroneous runs is put into a directory 'failure'. An erroneous run means that
the tool crashed or a timeout occured.

