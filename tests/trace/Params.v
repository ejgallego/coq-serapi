Class BaseParams :=
  {
    data : Type;
    input : Type;
    output : Type
  }.

Class MultiParams (P : BaseParams) :=
  {
    name : Type ;
    msg : Type ;
    init_handlers : name -> data;
  }.

Section StepAsync.
  Context `{params : MultiParams}.

  Record packet := mkPacket { pSrc  : name ; pDst  : name ; pBody : msg }.
End StepAsync.
