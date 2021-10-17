## Contributing to SerAPI

Thanks for willing to contribute to SerAPI! Contributing is usually as
easy as opening a pull request, issue, or dropping by the Gitter
channel and letting us know what you think of the tool.

Nothing special has to be kept in mind, other than standard OCaml
practice, we usually follow `ocp-indent` guidelines, but we are
liberal in some places in particular with regards to intra-line
indentation.

We prefer GPG signed commits as well as `Signed-off-by` commits.

## Releasing SerAPI

As of today, SerAPI is released using a standard process based on
`dune-release`; to do a release, it should suffice to do:

```
$ dune-release tag $version
$ dune-release
```

where `$version` is `$coq-version+$serapi_version`, for example
`8.16.2+0.16.4`. Note that `dune-release` requires you to setup a
github token, see `dune-release` docs for more details.

**Important**: note that `dune-release` will automatically generate
the changelog from `CHANGES.md`, please keep the formatting tidy in
that file!

Note that bug https://github.com/ejgallego/coq-serapi/issues/208 may
require you to edit the opam-repository PR if their linter fails
[seems fixed as of today, but OMMV]

### Commit tag conventions [work in progress]:

We have somme

- [serlib]  : Serialization lib.
- [test]    : Adding or modifying a test.
- [sertop]  : Sexp Toplevel.
- [doc]     : Documentation.
- [build]   : Build system.
- [misc]    : Code refactoring, miscellanenous
- [proto]   : Core protocol.
- [control] : STM protocol.
- [query]   : Query protocol.
- [parse]   : Parsing protocol.
- [print]   : Printing protocol.
- [js]      : Javascript version.
