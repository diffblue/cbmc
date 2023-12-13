
[//]: # if CBMC has a logo, it should go here.

CBMC is a Bounded Model Checker for C and C++ programs. It supports C89, C99,
most of C11 and most compiler extensions provided by gcc and Visual Studio. It
also supports SystemC using Scoot. It allows verifying array bounds (buffer
overflows), pointer safety, exceptions and user-specified assertions.
Furthermore, it can check C and C++ for consistency with other languages, such
as Verilog. The verification is performed by unwinding the loops in the program
and passing the resulting equation to a decision procedure.

[![Build Status][coverity_img]][coverity]
[![Build Status][codecov_img]][codecov]


## Installing

[//]: # The CBMC release page has the information about installation across all platforms.
[//]: # We don't need to repeat this information here, we just need to redirect the user with a better introduction here.

Get the [latest release](https://github.com/diffblue/cbmc/releases).
* Releases are tested and for production use.

Get the current *develop* version: `git clone https://github.com/diffblue/cbmc.git`.
* Develop versions are not recommended for production use.

## Documentation
[//]: # Here is a small introduction about user and developer documentation. We should point the user to a different page, which in this case could be the starter-kit.

[//]: # Should we explain the difference between CPROVER and the other source of documentations here? I would prefer not. Just focusing on CBMC and the different tools it provides.

### Features
[//]: # This is the section where we can guide the user on how they could use CBMC and the different tools it provides. I don't think we need to go over all of them, but it'd be nice to give the user a small example to help them understand what it is available.

## Reporting bugs
===========

If you encounter a problem please file a bug report:
* Create an [issue](https://github.com/diffblue/cbmc/issues)

## Contributing to CBMC

[//]: # We should replace this entire text here by a page about contributions.
If you are interested in contributing to CBMC, please see our [development guide]().

1. Fork the repository
2. Clone the repository `git clone git@github.com:YOURNAME/cbmc.git`
3. Create a branch from the `develop` branch (default branch)
4. Make your changes (follow the [coding guidelines](https://github.com/diffblue/cbmc/blob/develop/CODING_STANDARD.md))
5. Push your changes to your branch
6. Create a Pull Request targeting the `develop` branch

New contributors can look through the [mini
projects](https://github.com/diffblue/cbmc/blob/develop/FEATURE_IDEAS.md)
page for small, focussed feature ideas.

## License

[//]: # We need a link to the license file here. I'd keep this section.

4-clause BSD license, see `LICENSE` file.


[codebuild]: https://us-east-1.console.aws.amazon.com/codesuite/codebuild/projects/cbmc/history?region=us-east-1
[codebuild_img]: https://codebuild.us-east-1.amazonaws.com/badges?uuid=eyJlbmNyeXB0ZWREYXRhIjoiajhxcmNGUEgyV0xZa2ZFaVd3czJmbm1DdEt3QVdJRVdZaGJuMTUwOHFrZUM3eERwS1g4VEQ3Ymw3bmFncldVQXArajlYL1pXbGZNVTdXdndzUHU4Ly9JPSIsIml2UGFyYW1ldGVyU3BlYyI6IkVUUEdWVEt0SUFONlhyNVAiLCJtYXRlcmlhbFNldFNlcmlhbCI6MX0%3D&branch=develop
[codebuild_windows]: https://us-east-1.console.aws.amazon.com/codesuite/codebuild/projects/cbmc-windows/history?region=us-east-1
[codebuild_windows_img]: https://codebuild.us-east-1.amazonaws.com/badges?uuid=eyJlbmNyeXB0ZWREYXRhIjoiTFQ4Q0lCSEc1Rk5NcmlzaFZDdU44Vk8zY0c1VCtIVWMwWnJMRitmVFI5bE94Q3dhekVPMWRobFU2Q0xTTlpDSWZUQ3J1eksrWW1rSll1OExXdll2bExZPSIsIml2UGFyYW1ldGVyU3BlYyI6InpqcloyaEdxbjBiQUtvNysiLCJtYXRlcmlhbFNldFNlcmlhbCI6MX0%3D&branch=develop
[coverity]: https://scan.coverity.com/projects/diffblue-cbmc
[coverity_img]: https://scan.coverity.com/projects/13552/badge.svg
[codecov]: https://codecov.io/gh/diffblue/cbmc
[codecov_img]: https://codecov.io/gh/diffblue/cbmc/branch/develop/graphs/badge.svg
