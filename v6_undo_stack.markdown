# Temporary changes for v6

This is a temporary file, containing changes done to release process for v6,
that need to be reverted back.

It's a file in the repository to allow for easier tracking of the status
of things among the broader community, and to allow everyone to add/delete
things they believe should be in here.

The file is scheduled for deletion by the actual release of `v6` and subsequent
rollback of the changes.

## Stack

* Revert changes to homebrew PR push (`.github/workflows/release-packages.yaml`)
* Revert changes to docker image push (`.github/workflows/releas-packages.yaml`)
* Remove marking of release as `prerelease` (`.github/workflows/regular-release.yaml`)
