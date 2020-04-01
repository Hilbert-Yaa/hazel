module HoleReason = {
  /* Variable: reason */
  // TODO rename Keyword to ExpandingKeyword
  [@deriving sexp]
  type t =
    | Free
    | Keyword(ExpandingKeyword.t)
    | Duplicate;
};

/* Variable: var_err */
[@deriving sexp]
type t =
  | NotInVarHole
  | InVarHole(HoleReason.t, MetaVar.t);
