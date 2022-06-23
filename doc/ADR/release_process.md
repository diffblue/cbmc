# Release Process

**Date**: 2020-10-08
**Updated**: 2022-06-23
**Author**: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com
**Domain**: Release & Packaging

## Process

The current process we follow through to make a new release is the following:

1. At the point in time we want to make the release, we make a change to 
   `src/config.inc`, and update the configuration variable `CBMC_VERSION`.
   This is important as it informs the various tools of the current version
   of CBMC.

   (This needs to be pushed as a PR, and after it gets merged we move on to:)

2. Then we make a `git tag` out of that commit, and push it to github. The
   tag needs to be of the form `cbmc-<version>` with version being a version
   number of the form of `x.y.z`, with `x` denoting the major version, `y`
   denoting the minor version, and `z` identifying the patch version (useful
   for a hotfix or patch.)

At this point, the rest of the process is automated, so we don't need to do
anything more, but the process is described below for reference:

3. `.github/workflows/regular-release.yaml` gets triggered on the `push`
   of the tag, and creates a Github release of the version that was
   described in the tag pushed (so, tag `cbmc-5.15.20` is going to
   create the release titled `cbmc-5.15.20` on the release page).

4. `.github/workflows/release-packages.yaml` gets triggered automatically
   at the creation of the release, and its job is to build packages for
   Windows, Ubuntu 18.04 and Ubuntu 20.04 (for now, we may support more
   specific Ubuntu versions later) and attaches them (after it has finished
   building them) to the release page as release artifacts.

   It also makes a PR to the homebrew repository that updates the version
   of CBMC in homebrew. That's then approved and merged by the maintainers
   of homebrew.

## Versioning

We adopt an approach approximating SemVer. That is, our version numbers should
be major.minor.patch. Regular releases (as of 2022-06-23: every other week)
should normally increment the minor version number. This is also where we can
deprecate undesired features, i.e., mark as deprecated, warn existing users.

Patch version increments should not be done as part of the regular releases, and
instead should be reserved for critical bugfixes and issues noticed in the
process of doing a regular release. Don't make a patch release if you're not
confident your release contains nothing but bugfixes.

Major version increments should be reserved for changes which we expect will
break downstream users scripts and/or workflows. This includes things like
changing the goto binary format in such a way that old outputs can't be read by
new version of our tools or vice versa, or removing deprecated functionality
(removal of functionality should generally be preceded by deprecation!). Note
that incrementing the major version every time a change technically could break
a downstream users scripts would lead to a weak signal, as basically any
detectable change including bugfixes can do that. Instead, major version
increments should signal that we expect many users will have to review their
workflows for potential breakages, not just any.

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
