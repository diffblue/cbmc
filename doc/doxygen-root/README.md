# CBMC documentation

This is the root of CBMC documentation.

## Install doxygen

Building this documentation requires `doxygen` and `graphviz`.

* On MacOS,
  we recommend installing with [brew](https://brew.sh/):
  ```
  brew install doxygen graphviz
  ```
* On Ubuntu, we recommend installing with using `apt`:
  ```
  sudo apt install doxygen graphviz
  ```

Note: As of

## Build the documentation

To build the documentation, run

```
doxygen
```

The documentation takes about five minutes to build and is written to
the `html` subdirectory as a set of 2600+ html files.  To view the
documentation,
open the file `html/index.html` in a web browser.  One MacOS, run

```
open html/index.html
```

## Publish the documentation

To publish the documentation, we use the GitHub workflow
[publish.yaml](../../.github/workflow/publish.yaml) that
publishes the contents of the `html` subdirectory to
the `github.io` web site.

## Contribute documentation

Coming soon...

## References

* The cprover documentation: http://cprover.diffblue.com/
  * Sources: https://github.com/diffblue/cbmc/tree/develop/doc

* The cprover manual: http://www.cprover.org/cprover-manual/
  * Sources: https://github.com/diffblue/cbmc/tree/develop/doc/cprover-manual

* Doxygen manual: https://www.doxygen.nl/manual
  * Grouping documentation: https://www.doxygen.nl/manual/grouping.html
  * Markdown support: https://doxygen.nl/manual/markdown.html
  * Doxygen treatment of markdown pages: https://doxygen.nl/manual/markdown.html#markdown_dox