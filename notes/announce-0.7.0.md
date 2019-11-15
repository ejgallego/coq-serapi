Subject: [ANNOUNCE] SerAPI 0.7.0

Dear Coq users and developers,

we are happy to announce the release SerAPI 0.7.0 for Coq 8.10.

SerAPI provides an S-expression based API suitable for machine
interaction with Coq. Capabilities include full round-trip
serialization of Coq's AST and most internal structures, easy access
to the document build and checking API, and facilities for querying
Coq's environment and proof state.

SerAPI is developed by Emilio J. Gallego Arias, Karl Palmskog, and
many other contributors. SerAPI is free software. please don't
hesitate to report issues and contribute at:

- https://github.com/ejgallego/coq-serapi

## SerAPI 0.7.0

The 0.7.0 release provides brings many small improvements, bugfixes,
and tweaks; two highlights of the 0.7.0 release are:

  - it is now possible to serialize from/to `JSON` using the `Serlib` API
  - `sertok` command-line tool provides batch tokenization of Coq documents

See more information and examples on the project's website
https://github.com/ejgallego/coq-serapi, the full list of changes is
at https://github.com/ejgallego/coq-serapi/blob/v8.10/CHANGES.md

Items marked with `(!)` are protocol-breaking changes.

Best regards,
Emilio, Karl & all contributors
