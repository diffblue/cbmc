\page contributing_documentation Contributing documentation

The CBMC documentation is a work in progress.  The quality of the
documentation depends on contributions from users and developers.

Every markdown file in the repository contributes a page to the
doxygen output.  By default, a page will appear at the top-level
of the tree view of the documentation on the left side of every page
produced by doxygen.  You can use the `\page` and `\subpage` doxygen
commands to control where a page appears in this tree view.

If you want `child.md` to appear as a subpage of `parent.md` in the
documentation, you can add
```
\page child Child Page Title
```
to the top of `child.md` and add
```
\subpage child
```
at the appropriate place in `parent.md`.  The `\subpage` command will
have the effect of creating a link named "Child Page Title" to
`child.md` in `parent.md`.  In other places (and other files),
you can generate a link to `child.md` with `\ref child "link text"`.
The "link text" defaults to "Child Page Title".

When you contribute a module `mymodule.c` to the source code, there are
probably at least two kinds of documentation you want to contribute.
One is user documentation to help people use your feature.  One is
developer documentation to help people debug or extend your work.  We
recommend that you put files `mymodule-user.md` and `mymodule-developer.md`
next to `mymodule.c` in the repository.  Then you can use the `\page`
and `\subpage` mechanism described above into the appropriate parts of
the user guide and developer guide.

When you contribute documentation, it may not be clear whether it should
go into the user guide or the developer guide.  We recommend that you
put into the user guide everything a user needs to know to use the tool.
For example, put a description of the CBMC memory model into the
user guide.  Then the developer guide can link to that description of the
memory model in the user guide, and say, "This is the memory model, and
this is how we implement the memory model."
