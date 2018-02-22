let init ~omit_loc ~omit_att =
  Ser_loc.omit_loc  := omit_loc;
  Ser_cAst.omit_att := omit_att;
  ()
