open Pretty;

type t = Doc.t(HTypAnnot.t);

type formattable_child = (~enforce_inline: bool) => t;

let precedence_const = 0;
let precedence_Prod = 1;
let precedence_Sum = 2;
let precedence_Arrow = 3;
let precedence = (ty: HTyp.t): int =>
  switch (ty) {
  | Int
  | Float
  | Bool
  | Hole
  | Unit
  | List(_) => precedence_const
  | Prod(_, _) => precedence_Prod
  | Sum(_, _) => precedence_Sum
  | Arrow(_, _) => precedence_Arrow
  };

let pad_child =
    (
      ~inline_padding as (l, r)=(Doc.empty(), Doc.empty()),
      ~enforce_inline: bool,
      child: formattable_child,
    )
    : t => {
  let inline_choice = Doc.hcats([l, child(~enforce_inline=true), r]);
  let para_choice =
    Doc.(
      hcats([
        linebreak(),
        indent_and_align(child(~enforce_inline=false)),
        linebreak(),
      ])
    );
  enforce_inline ? inline_choice : Doc.choice(inline_choice, para_choice);
};

let mk_delim = s => Doc.(annot(HTypAnnot.Delim, text(s)));

let rec mk = (~parenthesize=false, ~enforce_inline: bool, ty: HTyp.t): t => {
  open Doc;
  let mk' = mk(~enforce_inline);
  let mk_right_associative_operands = (precedence_op, ty1, ty2) => (
    mk'(~parenthesize=precedence(ty1) >= precedence_op, ty1),
    mk'(~parenthesize=precedence(ty2) > precedence_op, ty2),
  );
  let doc =
    switch (ty) {
    | Hole => annot(HTypAnnot.Delim, annot(HTypAnnot.HoleLabel, text("?")))
    | Unit => text("()")
    | Int => text("Int")
    | Float => text("Float")
    | Bool => text("Bool")
    | List(ty) =>
      hcats([
        mk_delim("["),
        mk(ty) |> pad_child(~enforce_inline),
        mk_delim("]"),
      ])
    | Arrow(ty1, ty2) =>
      let (d1, d2) =
        mk_right_associative_operands(precedence_Arrow, ty1, ty2);
      hcats([
        d1,
        hcats([
          choices([linebreak(), space()]),
          text(UnicodeConstants.typeArrowSym ++ " "),
        ]),
        d2,
      ]);
    | Prod(ty1, ty2) =>
      let (d1, d2) =
        mk_right_associative_operands(precedence_Prod, ty1, ty2);
      hcats([d1, hcats([text(","), choices([linebreak(), space()])]), d2]);
    | Sum(ty1, ty2) =>
      let (d1, d2) = mk_right_associative_operands(precedence_Sum, ty1, ty2);
      hcats([
        d1,
        hcats([choices([linebreak(), space()]), text("| ")]),
        d2,
      ]);
    };
  parenthesize ? Doc.hcats([mk_delim("("), doc, mk_delim(")")]) : doc;
};
