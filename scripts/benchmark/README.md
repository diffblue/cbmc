Script to run an executable (for instance JBMC) on a list of Java methods.

# Install

    npm install

# Usage

    benchmark_java_project.js --help

# Example

Assuming there is a java maven module installed in `project-name/module-core/`,
and the `jbmc` main directory is in `/path/to/jbmc`, go to
`project-name/module-core/target/classes`, and run:

    /path/to/scripts/benchmark/benchmark_java_project.js /path/to/jbmc -l method_list_example.txt -a jbmc_arguments_example.json -m path/to/jbmc/lib/java-models-library/target/core-models.jar | tee result.json

This will display the results and save them into the file `result.json`.

The `method_list_example.txt` file provided here works for `apache-tika/tika-core` available from https://github.com/apache/tika

# Converting the result to csv

    ./benchmark_to_spreadsheet.js result.json >result.csv

This will create a `result.csv` file containing the results.

# Comparing two runs

Assuming the results have been converted to csv and saved into two files named
develop.csv and branch.csv:

     gnuplot draw_scatter.gp

will create a png file `perf_out.png` with the time from the branch / changed run on the
`y` axis and the develop / original run on the `x` axis.
