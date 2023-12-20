# CBMC release process

This document outlines the current release process in a summary form.

## Part I

1. PR with version label change to `src/config.inc` and `src/libcprover-rust/Cargo.toml`.
   To be merged after CI has run.
   * We update both with the same version after a decision had been made to keep both
     projects to the same version number. For more info on versioning, please take a look at
     `doc/ADR/release_process.md`

2. After the PR has been merged, pull develop locally and spin off a tag with
   `git tag -a cbmc-<version>`. After some wait, this is going to trigger building
   Linux && Windows jobs and submit PR to [`homebrew`](https://formulae.brew.sh/formula/cbmc)
   and image to [`docker`](https://hub.docker.com/r/diffblue/cbmc/tags).
   * The release creation is being driven by the `.github/workflows/regular-release.yaml` file,
     which creates a new release with some template text filled in.
   * After the release has been created, another github action starts building the
     binaries, driven by the `.github/workflows/release-packages.yaml`.

## Part II

1. Tap release performed next day depending on when homebrew formula has been updated.
   Process outlined at `doc/ADR/homebrew_tap.md`.
   * The process usually goes as follows: we give homebrew about a day after the release
     has been created to merge the PR updating the formula on their end, and for the
     bottles (binaries) to be built.
   * We update the `brew` database locally, and then extract the formula as outlined
     above (should be a command like `brew extract cbmc@version`).
   * After the formula has been extracted, we need to fetch the binaries they have built
     and edit the formula to contain the binaries and their hashes. We usually use
     the script [`transform_binary.sh`](https://github.com/diffblue/homebrew-cbmc/blob/main/transform_binary.sh)
     which downloads the bottles on the local folder and then gives us their hashes
     to edit the formula with. The end result looks like this: [Example formula](https://github.com/diffblue/homebrew-cbmc/commit/97e539b25465077304c6e8c01400b708511ed5ee)
   * Last bit is to commit the formula and push it to the tap, and edit the release to
     add the downloaded binaries as release artefacts. This last bit is just an edit
     of the `bag-of-goodies` release from the Github UI, and then a drag-and-drop of
     the binaries into the upload form.

2. Crates.io release which is really just a cargo publish with the environment
   variables the Rust build requires. Process outlined at https://docs.rs/crate/libcprover_rust/latest.
   * Usually this is just a `cargo publish --dry-run` first, waiting to see that
     the build is successful and that the command is aborting right before the
     build is uploaded, and then just performing a `cargo publish` which pushes
     the crate.
