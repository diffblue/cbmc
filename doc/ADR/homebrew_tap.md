# Homebrew tap instructions

CBMC archives versions into a tap which you can use to quickly download and
build various historical versions.

The tap is available at https://github.com/diffblue/homebrew-cbmc.

Any version installed from the tap will need to be built from source locally.

## Managing `brew tap`-based CBMC installations

* Add the CBMC tap using the following command:

  ```sh
  $ brew tap diffblue/cbmc
  ```

* Install any of the available CBMC versions in the following manner:

  ```sh
  $ brew install diffblue/cbmc/cbmc@5.54.0
  ```

* To remove the version of CBMC installed you need to issue

  ```sh
  $ brew remove diffblue/cbmc/cbmc@5.54.0
  ```

* To remove the tap altogether, you need to issue

  ```sh
  $ brew untap diffblue/cbmc
  ```

## CBMC maintainer instructions

* You can clone the [CBMC tap](https://github.com/diffblue/homebrew-cbmc)
  locally by issuing:

  ```sh
  $ brew tap diffblue/cbmc
  ```

  That instruction is going to clone the above tap repository locally.
  Afterwards, you can proceed with installing the formulas present,
  edit them, etc.

  If you wish to set up a new tap for any reason, you can
  use `brew tap-new` like the following example:

  ```sh
  $ brew tap-new <developer>/homebrew_cbmc
  ```

* For any edit, the second step is to `cd` into the repository.
  To do that easily, it's best to ask Homebrew to give you the
  location of the repository:

  ```sh
  $ cd $(brew --repo diffblue/cbmc)
  ```

* You can extract versions of CBMC previously available in `homebrew/core`
  to the tap with the following instruction:

  ```sh
  $ brew extract cbmc diffblue/cbmc --version=<ver>
  ```

  For example `$ brew extract cbmc diffblue/cbmc --version=5.54.0` will
  have as an end result a new file under `Formula/cbmc@5.54.0.rb` that will
  contain the formula that we had submitted for that version of CBMC in the
  `homebrew/core` repository.

* If you want to edit a specific version formula, you can do that by issueing

  ```sh
  $ brew edit cbmc@5.54.0
  ```

  with the appropriate version tag. This will open the formula on the default
  editor in your system to allow you to make changes.

  These changes are only going to be reflected locally - but you can `cd` to the
  repository, commit and then push to the tap (this is allowed only for people
  who have permission to push to the tap - mainly, the Diffblue open source team).

## Notes

* Bootstrapping the repository with `brew tap --new` created two github actions
  `.github/workflows/publish.yml` and `.github/workflows/tests.yml` which we are
  not using at the moment but could serve to make future automation easier.

## Known Limitations

* Different CBMC versions can co-exist in the same machine, but homebrew needs
  a symbolic link to be established because of how it manages the `$PATH` and
  installation directories for binaries.
* If already have a version of CBMC from the tap installed, and you want to
  install another version, then you need to take an extra step after installation
  to setup the appropriate symlinks by using the `brew link` instruction:

  ```sh
  $ cbmc --version   # version installed by brew
  5.54.0
  $ brew install diffblue/cbmc/cbmc@5.55.0
  $ brew link --overwrite cbmc@5.55.0
  $ cbmc --version
  5.55.0
  ```
