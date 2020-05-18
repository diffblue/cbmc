Left to do:
* Make the Debian builds run the full debian package flow.
* Refactor the workflow to invoke a makefile that can be invoked either from
  the workflow or from a command line to build the package.
* Make the workflow distinguish between stable versions and latest versions
  Stable versions should write into cbmc (or bin) and latest versions
  should write into cbmc-latest (so they can exist side-by-side).  Windows
  packages will have to have different product guids for stable and latest.
* Transform version numbers from 5.12 to 5.12.0.id where id is some value
  that increments with each build.  A good candidate is `github.run_id` or
  `github.run_num`.
* Can we automate the generation of repository packages (eg, homebrew)?

Plans:
* Wait for Michael's Debian builds and fit them into the workflow
* Refactor the workflow to invoke Makefiles
* Prepare PR
* Do remaining items as PR refinements.
