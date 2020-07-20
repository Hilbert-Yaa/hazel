[@deriving sexp]
type t =
  | Arrow
  | Prod
  | Sum;

let to_string =
  fun
  | Arrow => UnicodeConstants.typeArrowSym
  | Prod => ","
  | Sum => "|";

let to_parse_string = op =>
  switch (op) {
  | Arrow => "->"
  | _ => to_string(op)
  };

let precedence =
  fun
  | Arrow => 0
  | Sum => 1
  | Prod => 2;

let associativity =
  fun
  | Arrow => Associativity.Right
  | _ => Associativity.Left;
