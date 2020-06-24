[@deriving sexp]
type t =
  | Rule
  | Case({err: CaseErrStatus.t})
  | Var({
      err: ErrStatus.t,
      verr: VarErrStatus.t,
      show_use: bool,
    })
  | Operand({err: ErrStatus.t})
  | BinOp({
      op_index: int,
      err: ErrStatus.t,
    })
  | NTuple({
      comma_indices: list(int),
      err: ErrStatus.t,
    })
  | SubBlock({hd_index: int});

let mk_Var:
  (~err: ErrStatus.t=?, ~verr: VarErrStatus.t=?, ~show_use: bool=?, unit) => t;

let mk_Operand: (~err: ErrStatus.t=?, unit) => t;
