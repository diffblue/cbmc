# Release Process

**Date**: 8-10-2020
**Author**: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com
**Domain**: Release & Packaging

## Process

The current process we follow through to make a new release is the following:

1. At the point in time we want to make the release, we make a change to 
   `src/config.inc`, and update the configuration variable `CBMC_VERSION`.
   This is important as it informs the various tools of the current version
   of CBMC. The commit message must then contain one of #major, #minor, or
   #patch to inform the GitHub action that automatically creates a release tag.
   The tag is of the form `cbmc-<version>`, with `<version>` being a version
   number of the form of `x.y.z`, with `x` denoting the major version, `y`
   denoting the minor version, and `z` identifying the patch version (useful
   for a hotfix or patch.)

At this point, the rest of the process is automated, so we don't need to do
anything more, but the process is described below for reference:

2. `.github/workflows/regular-release.yaml` gets triggered on the `push`
   of the tag, and creates a Github release of the version that was
   described in thetag pushed (so, tag `cbmc-5.15.20` is going to
   create the release titled `cbmc-5.15.20` on the release page).

3. `.github/workflows/release-packages.yaml` gets triggered automatically
   at the creation of the release, and its job is to build packages for
   Windows, Ubuntu 18.04 and Ubuntu 20.04 (for now, we may support more
   specific Ubuntu versions later) and attaches them (after it has finished
   building them) to the release page as release artifacts. 

   It also makes a PR to the homebrew repository that updates the version
   of CBMC in homebrew. That's then approved and merged by the maintainers
   of homebrew.

## Constraints

Initial design of the release process suggested that the release cadence
of CBMC was going to be one regular release (incrementing the `y` part
of the version) every two weeks, on Thursday.

Originally we wanted to automate this part, but we were limited by the
fact that we needed to update `src/config.inc` before doing the release,
and that couldn't be done in an automated fashion, as any update needs
to go through a PR, and gets stuck on code-owners approvals, making the
whole process more manual than intended.

Following this original limitation, we decided to settle on doing manual
releases every two weeks, but having the process being initiated by a
developer manually making the change to `src/config.inc`, and after that
has been merged, mark that specific commit as with a version tag, and push
that version tag to Github. At that point, the rest of the process is automated.

The change to the current implementation was part of https://github.com/diffblue/cbmc/pull/5517.
