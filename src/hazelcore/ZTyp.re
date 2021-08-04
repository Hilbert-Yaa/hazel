open OptUtil.Syntax;

[@deriving sexp]
type zsumbody_operator = (CursorPosition.t, Operators_SumBody.t);

[@deriving sexp]
type t = zopseq
and zopseq = ZOpSeq.t(UHTyp.operand, UHTyp.operator, zoperand, zoperator)
and zoperand =
  | CursorT(CursorPosition.t, UHTyp.operand)
  | ParenthesizedZ(t)
  | SumZ(zsumbody)
  | ListZ(t)
and zoperator = (CursorPosition.t, UHTyp.operator)
and zsumbody =
  ZOpSeq.t(
    UHTyp.sumbody_operand,
    UHTyp.sumbody_operator,
    zsumbody_operand,
    zsumbody_operator,
  )
// TODO: replace CursorTS with base case for ArgTag delims
and zsumbody_operand =
  | CursorTS(CursorPosition.t, UHTyp.sumbody_operand)
  | ConstTagZ(ZTag.t)
  | ArgTagZT(ZTag.t, UHTyp.t)
  | ArgTagZA(UHTag.t, t);

type operand_surround = Seq.operand_surround(UHTyp.operand, UHTyp.operator);
type operator_surround = Seq.operator_surround(UHTyp.operand, UHTyp.operator);
type zseq = ZSeq.t(UHTyp.operand, UHTyp.operator, zoperand, zoperator);

type sumbody_operand_surround =
  Seq.operand_surround(UHTyp.sumbody_operand, UHTyp.sumbody_operator);
type sumbody_operator_surround =
  Seq.operator_surround(UHTyp.sumbody_operand, UHTyp.sumbody_operator);
type sumbody_zseq =
  ZSeq.t(
    UHTyp.sumbody_operand,
    UHTyp.sumbody_operator,
    zsumbody_operand,
    zsumbody_operator,
  );

let valid_cursors_operand: UHTyp.operand => list(CursorPosition.t) =
  fun
  | Hole
  | Unit
  | Int
  | Float
  | Bool => CursorPosition.delim_cursors(1)
  | Parenthesized(_)
  | Sum(_)
  | List(_) => CursorPosition.delim_cursors(2);

let valid_cursors_operator: UHTyp.operator => list(CursorPosition.t) =
  fun
  | _ => [OnOp(Before), OnOp(After)];

let valid_cursors_sumbody_operand:
  UHTyp.sumbody_operand => list(CursorPosition.t) =
  fun
  | ConstTag(_) => CursorPosition.delim_cursors(1)
  | ArgTag(_, _) => CursorPosition.delim_cursors(2);

let valid_cursors_sumbody_operator =
    (_: UHTyp.sumbody_operator): list(CursorPosition.t) => [
  OnOp(Before),
  OnOp(After),
];

let is_valid_cursor_operand =
    (cursor: CursorPosition.t, operand: UHTyp.operand): bool =>
  valid_cursors_operand(operand) |> List.mem(cursor);
let is_valid_cursor_operator =
    (cursor: CursorPosition.t, operator: UHTyp.operator): bool =>
  valid_cursors_operator(operator) |> List.mem(cursor);

let is_valid_cursor_sumbody_operand =
    (cursor: CursorPosition.t, sumty_operand: UHTyp.sumbody_operand): bool =>
  valid_cursors_sumbody_operand(sumty_operand) |> List.mem(cursor);
let is_valid_cursor_sumbody_operator =
    (cursor: CursorPosition.t, sumty_operator: UHTyp.sumbody_operator): bool =>
  valid_cursors_sumbody_operator(sumty_operator) |> List.mem(cursor);

let erase_zoperator =
  fun
  | (_, operator) => operator;
let erase_zsumbody_operator =
  fun
  | (_, sumty_op) => sumty_op;

let rec erase = (zty: t): UHTyp.t => zty |> erase_zopseq
and erase_zopseq = zopseq =>
  ZOpSeq.erase(~erase_zoperand, ~erase_zoperator, zopseq)
and erase_zoperand =
  fun
  | CursorT(_, operand) => operand
  | ParenthesizedZ(zty) => Parenthesized(erase(zty))
  | SumZ(zsumty) => Sum(erase_zsumbody(zsumty))
  | ListZ(zty) => List(erase(zty))
and erase_zsumbody = zsumty =>
  ZOpSeq.erase(
    ~erase_zoperand=erase_zsumbody_operand,
    ~erase_zoperator,
    zsumty,
  )
and erase_zsumbody_operand =
  fun
  | CursorTS(_, sumty_operand) => sumty_operand
  | ConstTagZ(ztag) => UHTyp.ConstTag(ZTag.erase(ztag))
  | ArgTagZT(ztag, ty) => UHTyp.ArgTag(ZTag.erase(ztag), ty)
  | ArgTagZA(tag, zty) => UHTyp.ArgTag(tag, erase(zty));

let mk_ZOpSeq: zseq => zopseq =
  ZOpSeq.mk(~associate=UHTyp.associate, ~erase_zoperand, ~erase_zoperator);

let mk_sumbody_ZOpSeq: sumbody_zseq => zsumbody =
  ZOpSeq.mk(
    ~associate=UHTyp.associate_sumbody,
    ~erase_zoperand=erase_zsumbody_operand,
    ~erase_zoperator=erase_zsumbody_operator,
  );

let erase_zseq = zseq =>
  zseq |> ZSeq.erase(~erase_zoperand, ~erase_zoperator);

let rec is_before = (zty: t): bool => zty |> is_before_zopseq
and is_before_zopseq = zopseq => ZOpSeq.is_before(~is_before_zoperand, zopseq)
and is_before_zoperand =
  fun
  | CursorT(cursor, Hole)
  | CursorT(cursor, Unit)
  | CursorT(cursor, Int)
  | CursorT(cursor, Float)
  | CursorT(cursor, Bool)
  | CursorT(cursor, Parenthesized(_))
  | CursorT(cursor, Sum(_))
  | CursorT(cursor, List(_)) => cursor == OnDelim(0, Before)
  | ParenthesizedZ(_)
  | SumZ(_)
  | ListZ(_) => false;
let is_before_zoperator: zoperator => bool =
  fun
  | (OnOp(Before), _) => true
  | _ => false;

let is_before_zsumbody_operand =
  fun
  | CursorTS(cursor, ConstTag(_) | ArgTag(_, _)) =>
    cursor == OnDelim(0, Before)
  | ConstTagZ(_)
  | ArgTagZT(_, _)
  | ArgTagZA(_, _) => false;

let is_before_zsumbody = (zsumty: zsumbody): bool =>
  ZOpSeq.is_before(~is_before_zoperand=is_before_zsumbody_operand, zsumty);

let rec is_after = (zty: t): bool => zty |> is_after_zopseq
and is_after_zopseq = zopseq => ZOpSeq.is_after(~is_after_zoperand, zopseq)
and is_after_zoperand =
  fun
  | CursorT(cursor, Hole)
  | CursorT(cursor, Unit)
  | CursorT(cursor, Int)
  | CursorT(cursor, Float)
  | CursorT(cursor, Bool) => cursor == OnDelim(0, After)
  | CursorT(cursor, Parenthesized(_))
  | CursorT(cursor, Sum(_))
  | CursorT(cursor, List(_)) => cursor == OnDelim(1, After)
  | ParenthesizedZ(_)
  | SumZ(_)
  | ListZ(_) => false;
let is_after_zoperator: zoperator => bool =
  fun
  | (OnOp(After), _) => true
  | _ => false;

let is_after_zsumbody_operand =
  fun
  | CursorTS(cursor, ConstTag(_)) => cursor == OnDelim(0, After)
  | CursorTS(cursor, ArgTag(_, _)) => cursor == OnDelim(1, After)
  | ConstTagZ(_) /* XXX => ZTag.is_after(??) */
  | ArgTagZT(_, _)
  | ArgTagZA(_, _) => false;

let is_after_zsumbody = (zsumty: zsumbody): bool =>
  ZOpSeq.is_after(~is_after_zoperand=is_after_zsumbody_operand, zsumty);

let rec place_before = (ty: UHTyp.t): t => ty |> place_before_opseq
and place_before_opseq = opseq =>
  ZOpSeq.place_before(~place_before_operand, opseq)
and place_before_operand =
  fun
  | (Hole | Unit | Int | Float | Bool | Parenthesized(_) | Sum(_) | List(_)) as operand =>
    CursorT(OnDelim(0, Before), operand);
let place_before_operator = (op: UHTyp.operator): option(zoperator) =>
  Some((OnOp(Before), op));

let place_before_sumbody_operand: UHTyp.sumbody_operand => zsumbody_operand =
  fun
  | UHTyp.ConstTag(tag) => ConstTagZ(ZTag.place_before(tag))
  | UHTyp.ArgTag(tag, ty) => ArgTagZT(ZTag.place_before(tag), ty);
let place_before_sumbody = (sumty: UHTyp.sumbody): zsumbody =>
  ZOpSeq.place_before(
    ~place_before_operand=place_before_sumbody_operand,
    sumty,
  );
let place_before_sumbody_operator =
    (sumty_op: UHTyp.sumbody_operator): option(zsumbody_operator) =>
  Some((OnOp(Before), sumty_op));

let rec place_after = (ty: UHTyp.t): t => ty |> place_after_opseq
and place_after_opseq = opseq =>
  ZOpSeq.place_after(~place_after_operand, opseq)
and place_after_operand =
  fun
  | (Hole | Unit | Int | Float | Bool) as operand =>
    CursorT(OnDelim(0, After), operand)
  | (Parenthesized(_) | Sum(_) | List(_)) as operand =>
    CursorT(OnDelim(1, After), operand);
let place_after_operator = (op: UHTyp.operator): option(zoperator) =>
  Some((OnOp(After), op));
let place_after_sumbody_operand =
    (sumty_operand: UHTyp.sumbody_operand): zsumbody_operand =>
  switch (sumty_operand) {
  | UHTyp.ConstTag(tag) => ConstTagZ(ZTag.place_after(tag))
  | UHTyp.ArgTag(tag, ty) => ArgTagZA(tag, place_after(ty))
  };
let place_after_sumbody = (sumty: UHTyp.sumbody): zsumbody =>
  ZOpSeq.place_after(~place_after_operand=place_after_sumbody_operand, sumty);
let place_after_sumbody_operator =
    (op: UHTyp.sumbody_operator): option(zsumbody_operator) =>
  Some((OnOp(After), op));

let place_cursor_operand =
    (cursor: CursorPosition.t, operand: UHTyp.operand): option(zoperand) =>
  is_valid_cursor_operand(cursor, operand)
    ? Some(CursorT(cursor, operand)) : None;
let place_cursor_operator =
    (cursor: CursorPosition.t, operator: UHTyp.operator): option(zoperator) =>
  is_valid_cursor_operator(cursor, operator)
    ? Some((cursor, operator)) : None;

let place_cursor_sumbody_operand =
    (cursor: CursorPosition.t, sumty_operand: UHTyp.sumbody_operand)
    : option(zsumbody_operand) =>
  is_valid_cursor_sumbody_operand(cursor, sumty_operand)
    ? Some(CursorTS(cursor, sumty_operand)) : None;
let place_cursor_sumbody_operator =
    (cursor: CursorPosition.t, sumty_operator: UHTyp.sumbody_operator)
    : option(zsumbody_operator) =>
  is_valid_cursor_sumbody_operator(cursor, sumty_operator)
    ? Some((cursor, sumty_operator)) : None;

let move_cursor_left_zoperator: zoperator => option(zoperator) =
  fun
  | (OnText(_) | OnDelim(_, _), _) => None
  | (OnOp(Before), _) => None
  | (OnOp(After), op) => Some((OnOp(Before), op));

let move_cursor_left_zsumbody_operator:
  zsumbody_operator => option(zsumbody_operator) =
  fun
  | (OnText(_) | OnDelim(_, _), _) => None
  | (OnOp(Before), _) => None
  | (OnOp(After), op) => Some((OnOp(Before), op));

let rec move_cursor_left = (zty: t): option(t) =>
  zty |> move_cursor_left_zopseq
and move_cursor_left_zopseq = zopseq =>
  ZOpSeq.move_cursor_left(
    ~move_cursor_left_zoperand,
    ~move_cursor_left_zoperator,
    ~place_after_operand,
    ~place_after_operator,
    ~erase_zoperand,
    ~erase_zoperator,
    zopseq,
  )
and move_cursor_left_zoperand =
  fun
  | z when is_before_zoperand(z) => None
  | CursorT(OnOp(_) | OnText(_), _) => None
  | CursorT(OnDelim(k, After), ty) =>
    Some(CursorT(OnDelim(k, Before), ty))
  | CursorT(OnDelim(_, Before), Hole | Unit | Int | Float | Bool) => None
  | CursorT(OnDelim(_k, Before), Parenthesized(ty1)) =>
    // _k == 1
    Some(ParenthesizedZ(place_after(ty1)))
  | CursorT(OnDelim(_k, Before), Sum(ty1)) =>
    // _k == 1
    Some(SumZ(place_after_sumbody(ty1)))
  | CursorT(OnDelim(_k, Before), List(ty1)) =>
    // _k == 1
    Some(ListZ(place_after(ty1)))
  | ParenthesizedZ(zty1) =>
    switch (move_cursor_left(zty1)) {
    | Some(zty1) => Some(ParenthesizedZ(zty1))
    | None => Some(CursorT(OnDelim(0, After), Parenthesized(erase(zty1))))
    }
  | SumZ(zsumty) =>
    switch (move_cursor_left_zsumbody(zsumty)) {
    | Some(zsumty) => Some(SumZ(zsumty))
    | None =>
      Some(CursorT(OnDelim(0, After), Sum(erase_zsumbody(zsumty))))
    }
  | ListZ(zty1) =>
    switch (move_cursor_left(zty1)) {
    | Some(zty1) => Some(ListZ(zty1))
    | None => Some(CursorT(OnDelim(0, After), List(erase(zty1))))
    }
and move_cursor_left_zsumbody = zsumty =>
  ZOpSeq.move_cursor_left(
    ~move_cursor_left_zoperand=move_cursor_left_zsumbody_operand,
    ~move_cursor_left_zoperator=move_cursor_left_zsumbody_operator,
    ~place_after_operand=place_after_sumbody_operand,
    ~place_after_operator=place_after_sumbody_operator,
    ~erase_zoperand=erase_zsumbody_operand,
    ~erase_zoperator=erase_zsumbody_operator,
    zsumty,
  )
and move_cursor_left_zsumbody_operand =
  fun
  | CursorTS(OnOp(_) | OnText(_), _) => None
  | CursorTS(OnDelim(_0, Before), ConstTag(_)) => None
  | CursorTS(OnDelim(0, Before), ArgTag(_, _)) => None
  | CursorTS(OnDelim(k, Before), ArgTag(_, _) as sumty_operand) =>
    Some(CursorTS(OnDelim(k - 1, After), sumty_operand))
  | CursorTS(OnDelim(_0, After), sumty_operand) =>
    Some(CursorTS(OnDelim(0, Before), sumty_operand))
  | ConstTagZ(ztag) => {
      let+ ztag = ZTag.move_cursor_left(ztag);
      ConstTagZ(ztag);
    }
  | ArgTagZT(ztag, ty) => {
      let+ ztag = ZTag.move_cursor_left(ztag);
      ArgTagZT(ztag, ty);
    }
  | ArgTagZA(tag, zty) => {
      let+ zty = move_cursor_left(zty);
      ArgTagZA(tag, zty);
    };

let move_cursor_right_zoperator: zoperator => option(zoperator) =
  fun
  | (OnText(_) | OnDelim(_, _), _) => None
  | (OnOp(After), _) => None
  | (OnOp(Before), op) => Some((OnOp(After), op));
let move_cursor_right_zsumbody_operator:
  zsumbody_operator => option(zsumbody_operator) =
  fun
  | (OnText(_) | OnDelim(_, _), _) => None
  | (OnOp(After), _) => None
  | (OnOp(Before), op) => Some((OnOp(After), op));

let rec move_cursor_right = (zty: t): option(t) =>
  zty |> move_cursor_right_zopseq
and move_cursor_right_zopseq = zopseq =>
  ZOpSeq.move_cursor_right(
    ~move_cursor_right_zoperand,
    ~move_cursor_right_zoperator,
    ~place_before_operand,
    ~place_before_operator,
    ~erase_zoperand,
    ~erase_zoperator,
    zopseq,
  )
and move_cursor_right_zoperand =
  fun
  | z when is_after_zoperand(z) => None
  | CursorT(OnOp(_) | OnText(_), _) => None
  | CursorT(OnDelim(k, Before), ty) =>
    Some(CursorT(OnDelim(k, After), ty))
  | CursorT(OnDelim(_, After), Hole | Unit | Int | Float | Bool) => None
  | CursorT(OnDelim(_k, After), Parenthesized(ty1)) =>
    // _k == 0
    Some(ParenthesizedZ(place_before(ty1)))
  | CursorT(OnDelim(_k, After), Sum(sumty)) =>
    // _k == 0
    Some(SumZ(place_before_sumbody(sumty)))
  | CursorT(OnDelim(_k, After), List(ty1)) =>
    // _k == 0
    Some(ListZ(place_before(ty1)))
  | ParenthesizedZ(zty1) =>
    switch (move_cursor_right(zty1)) {
    | Some(zty1) => Some(ParenthesizedZ(zty1))
    | None =>
      Some(CursorT(OnDelim(1, Before), Parenthesized(erase(zty1))))
    }
  | SumZ(zsumty) =>
    switch (move_cursor_right_zsumbody(zsumty)) {
    | Some(zsumty) => Some(SumZ(zsumty))
    | None =>
      Some(CursorT(OnDelim(1, Before), Sum(erase_zsumbody(zsumty))))
    }
  | ListZ(zty1) =>
    switch (move_cursor_right(zty1)) {
    | Some(zty1) => Some(ListZ(zty1))
    | None => Some(CursorT(OnDelim(1, Before), List(erase(zty1))))
    }
and move_cursor_right_zsumbody = zsumty =>
  ZOpSeq.move_cursor_right(
    ~move_cursor_right_zoperand=move_cursor_right_zsumbody_operand,
    ~move_cursor_right_zoperator=move_cursor_right_zsumbody_operator,
    ~place_before_operand=place_before_sumbody_operand,
    ~place_before_operator=place_before_sumbody_operator,
    ~erase_zoperand=erase_zsumbody_operand,
    ~erase_zoperator=erase_zsumbody_operator,
    zsumty,
  )
and move_cursor_right_zsumbody_operand =
  fun
  | CursorTS(OnOp(_) | OnText(_), _) => None
  | CursorTS(OnDelim(k, Before), sumty_operand) =>
    Some(CursorTS(OnDelim(k, After), sumty_operand))
  | CursorTS(OnDelim(_0, After), ConstTag(_)) => None
  | CursorTS(OnDelim(1, After), ArgTag(_)) => None
  | CursorTS(OnDelim(_0, After), ArgTag(_, _) as sumty_operand) =>
    Some(CursorTS(OnDelim(1, Before), sumty_operand))
  | ConstTagZ(ztag) => {
      let+ ztag = ZTag.move_cursor_right(ztag);
      ConstTagZ(ztag);
    }
  | ArgTagZT(ztag, ty) => {
      let+ ztag = ZTag.move_cursor_right(ztag);
      ArgTagZT(ztag, ty);
    }
  | ArgTagZA(tag, zty) => {
      let+ zty = move_cursor_right(zty);
      ArgTagZA(tag, zty);
    };
