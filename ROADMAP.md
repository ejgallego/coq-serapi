- Full document parsing. Full asynchronous `Add/Cancel` protocol.
  => Add a cache so users can efficiently send full documents.

- **[started]** Implement Locate -> "file name where the object is defined".

- Improve the handling of names and environments, see

  `Coq.Init.Notations.instantiate` vs `instantiate`, the issue of
  `Nametab.shortest_qualid_of_global` is a very sensible one for IDEs

   Maybe we could add some options `Short`, `Full`, `Best` ? ...
   Or we could even serialize the naming structure and let the ide decide if we export the current open namespace.

- Help with complex codepaths:
  Load Path parsing and completion code is probably one of the most complex part of company-coq

- Redo Query API, make Query language a GADT.

- Support regexps in queries.

- Would be easy to get a list of vernacs? Things like `Print`, `Typeclasses eauto`, etc.
  => ppx to enumerate datatypes. Write the help command with this and also Clément suggestions about Vernac enumeration.

- enable an open CoqObject tag for plugin use (see coq/coq#209 ) ?

- Checkstyle support.

- add bench option to queries commands XD
  basically (bench (any list of serapi commands))
  will return BenchData XD

- add commit with option for debug / backtrace mode.
- improve locate
