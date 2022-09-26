# CBMC documentation

This is the root of CBMC documentation.

## Install tools

Building this documentation requires `doxygen`, `graphviz`, and `pandoc`.

* On MacOS,
  we recommend installing with [brew](https://brew.sh/):
  ```
  brew install doxygen graphviz pandoc
  ```
* On Ubuntu, we recommend installing with using `apt`:
  ```
  sudo apt install doxygen graphviz pandoc
  ```

## Build the documentation

To build the documentation, run

```
make
```

The build takes about five minutes, and the documentation is written to
the `html` subdirectory as a mostly-flat collection of 2600+ html files.
To view the documentation,
open the file `html/index.html` in a web browser.  One MacOS, run

```
open html/index.html
```

The build will refuse to run if the repository is dirty
(if there are uncomitted changes).
The build appends "last modified" tags to the end of every markdown file,
which modifies about 60 markdown files.
Run `git checkout .` in the repository root to restore the markdown files
to their original state.

The build actually runs six builds:

* the legacy CPROVER documentation in `src` and `doc` which now includes the
  top-level pages in this directory,
* the legacy CPROVER manual in `doc/cprover-manual`,
* the man pages in `doc/man`,  and
* some supplemental documentation in `doc/API`, `doc/ADR`, and `doc/assets`.

## Publish the documentation

To publish the documentation, we use the GitHub workflow
[publish.yaml](../../.github/workflow/publish.yaml) that
publishes the contents of the `html` subdirectory to
the `github.io` web site.

## Contribute documentation

To contribute to this documentation,
there are some [documentation instructions](contributing.md) written
to make it easier for you to link your documentation into the right
location.


## References

* The cprover documentation: https://diffblue.github.io/cbmc/
  * Sources: https://github.com/diffblue/cbmc/tree/develop/doc

* The cprover manual: http://www.cprover.org/cprover-manual/
  * Sources: https://github.com/diffblue/cbmc/tree/develop/doc/cprover-manual

* Doxygen manual: https://www.doxygen.nl/manual
  * Grouping documentation: https://www.doxygen.nl/manual/grouping.html
  * Markdown support: https://doxygen.nl/manual/markdown.html
  * Doxygen treatment of markdown pages: https://doxygen.nl/manual/markdown.html#markdown_dox
