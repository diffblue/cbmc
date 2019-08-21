* Reduce the number of source files marked up
	* Add utility to generate a json list of source files used
	  (generate by building with the preprocessor and scanning the
	  result for source files; this solves the problem of multiple
	  builds giving conflicting symbol definitions).  Include sloc
	  data in the summary.
	* Use json list of source files as list of files to markup

* Improve accuracy of linking symbols to definitions
	* Add utility to generate json list of symbols definitions using
	  ctags instead of etags.
	* Use json list of source files as list of files to search for symbols
	* Modify markup to ignore comments and strings when looking for
	  strings to link to symbol definitions.

* Simplify coverage markup
    * Add utility to generate a json summary of coverage checking.

* Improve trace markup
	* Add utility to generate a json summary of property checking.
	* Major issue is that json output from CBMC is hard to translate
	  into a simple representation, and the json output does not include
	  the ascii string produced by the text output.

* Consider make regression tests run as ordinary regressions.  The
  remaining question is how to compare directories for equality on
  Windows like "diff -r" on Linux and MacOS.

* Use CSS files for markup instead of hardcoded, inlined style attributes.

* Cleanup error handling in tags.py and block.py.


