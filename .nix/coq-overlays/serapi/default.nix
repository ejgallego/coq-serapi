{ lib, fetchzip, mkCoqDerivation, coq, version ? null }:

let ocamlPackages =
      coq.ocamlPackages.overrideScope'
        (self: super: {
          ppxlib = super.ppxlib.override { version = "0.15.0"; };
          # the following does not work
          ppx_sexp_conv = super.ppx_sexp_conv.overrideAttrs (_: {
            src = fetchzip {
              url = "https://github.com/janestreet/ppx_sexp_conv/archive/v0.14.1.tar.gz";
              sha256 = "04bx5id99clrgvkg122nx03zig1m7igg75piphhyx04w33shgkz2";
            };
          });
        });
in

with lib; mkCoqDerivation {
  pname = "serapi";
  repo = "coq-serapi";
  owner = "ejgallego";
  inherit version;

  defaultVersion =  with versions; switch coq.version [
      { case = isEq "8.13"; out = "8.13.0+0.13.0"; }
      { case = isEq "8.12"; out = "8.12.0+0.12.1"; }
      { case = isEq "8.11"; out = "8.11.0+0.11.1"; }
      { case = isEq "8.10"; out = "8.10.0+0.7.2";  }
    ] null;

  release = {
    "8.13.0+0.13.0".sha256 = "0gq10z4gazzg101nvpcb34lljdv80pxwy6fnmfjapfvvbby2igs8";
    "8.12.0+0.12.1".sha256 = "1gcxjwiiyj89jnb81fvwlppv7bpwps6vh87y54jk24pr57qz4daw";
    "8.11.0+0.11.1".sha256 = "1k00rw7p35ngs5i1a1l1ddx31zhpb6yfrl9g0yi4cq93r2alwh1b";
    "8.10.0+0.7.2".sha256  = "0b95b0nxlmlgbpm79xkihjdhq3z3300n2hkbyilcnza8ppnp4r80";
  };

  useDune2 = true;
  mlPlugin = true;

  extraBuildInputs =
    with ocamlPackages; [
      cmdliner
      ppx_deriving
      ppx_deriving_yojson
      ppx_import
      ppx_sexp_conv
      sexplib
      yojson
    ];

  preInstall = "mkdir -p $out/lib/coq";

  meta = with lib; {
    homepage = https://github.com/ejgallego/coq-serapi;
    description = "SerAPI is a library for machine-to-machine interaction with the Coq proof assistant";
    license = licenses.lgpl21Plus;
    maintainers = [ maintainers.ptival maintainers.Zimmi48 ];
  };
}
