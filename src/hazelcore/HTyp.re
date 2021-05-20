open Sexplib.Std;

/* types with holes */
[@deriving sexp]
type t =
  | Hole
  // Don't want to remove label, still treat the same as hole type
  | Label(Label.t)
  | Int
  | Float
  | Bool
  | Arrow(t, t)
  | Sum(t, t)
  | Prod(list((option(Label.t), t)))
  | List(t);

[@deriving sexp]
type join =
  | GLB
  | LUB;

let precedence_Prod = Operators_Typ.precedence(Prod);
let precedence_Arrow = Operators_Typ.precedence(Arrow);
let precedence_Sum = Operators_Typ.precedence(Sum);
let precedence_Space = Operators_Typ.precedence(Space);
let precedence_const = Operators_Typ.precedence_const;

let precedence = (ty: t): int =>
  switch (ty) {
  | Int
  | Float
  | Bool
  | Hole
  | Prod([])
  | List(_)
  | Label(_) => precedence_const
  | Prod(_) => precedence_Prod
  | Sum(_, _) => precedence_Sum
  | Arrow(_, _) => precedence_Arrow
  };

/* equality
   At the moment, this coincides with default equality,
   but this will change when polymorphic types are implemented */
let eq = (==);

/* type consistency */
let rec consistent = (x, y) =>
  switch (x, y) {
  | (Hole, _)
  | (_, Hole)
  | (Label(_), _)
  | (_, Label(_)) => true
  | (Int, Int) => true
  | (Int, _) => false
  | (Float, Float) => true
  | (Float, _) => false
  | (Bool, Bool) => true
  | (Bool, _) => false
  | (Arrow(ty1, ty2), Arrow(ty1', ty2'))
  | (Sum(ty1, ty2), Sum(ty1', ty2')) =>
    consistent(ty1, ty1') && consistent(ty2, ty2')
  | (Arrow(_, _), _) => false
  | (Sum(_, _), _) => false
  | (Prod(tys1), Prod(tys2)) =>
    ListUtil.for_all2_opt(
      ((label1, ty1), (label2, ty2)) => {
        switch (label1, label2) {
        | (Some(l1), Some(l2)) => l1 == l2 && consistent(ty1, ty2)
        | (None, None) => consistent(ty1, ty2)
        | (Some(_), None)
        | (None, Some(_)) => false
        }
      },
      tys1,
      tys2,
    )
    |> Option.value(~default=false)
  | (Prod(_), _) => false
  | (List(ty), List(ty')) => consistent(ty, ty')
  | (List(_), _) => false
  };

let inconsistent = (ty1, ty2) => !consistent(ty1, ty2);

let rec consistent_all = (types: list(t)): bool =>
  switch (types) {
  | [] => true
  | [hd, ...tl] =>
    if (List.exists(inconsistent(hd), tl)) {
      false;
    } else {
      consistent_all(tl);
    }
  };

/* matched arrow types */
let matched_arrow =
  fun
  | Hole => Some((Hole, Hole))
  | Arrow(ty1, ty2) => Some((ty1, ty2))
  | _ => None;

// ECD TODO: Figure out if the label needs to be sent along in the get prod elements
// or if it can be ignored
let get_prod_elements: t => list(t) =
  fun
  | Prod(tys) => List.map(((label, ty)) => {ty}, tys)
  | _ as ty => [ty];

let get_prod_arity = ty => ty |> get_prod_elements |> List.length;

let rec get_projected_type = (ty: t, l: Label.t): option(t) => {
  switch (ty) {
  | Prod([]) => None
  | Prod(tys) =>
    List.find_opt(
      ((label, ty)) => {
        switch (label) {
        | Some(l') => l' == l
        | None => false
        }
      },
      tys,
    )
    |> Option.map(((label, ty)) => ty)
  | Hole => Some(Hole)
  | _ => None
  };
};

/* matched sum types */
let matched_sum =
  fun
  | Hole => Some((Hole, Hole))
  | Sum(tyL, tyR) => Some((tyL, tyR))
  | _ => None;

/* matched list types */
let matched_list =
  fun
  | Hole => Some(Hole)
  | List(ty) => Some(ty)
  | _ => None;

/* complete (i.e. does not have any holes) */
let rec complete =
  fun
  | Hole => false
  | Int => true
  | Float => true
  | Bool => true
  | Label(_) => false
  | Arrow(ty1, ty2)
  | Sum(ty1, ty2) => complete(ty1) && complete(ty2)
  | Prod(tys) => tys |> List.for_all(((label, ty)) => complete(ty))
  | List(ty) => complete(ty);

let rec join = (j, ty1, ty2) =>
  switch (ty1, ty2) {
  | (_, Hole | Label(_)) =>
    switch (j) {
    | GLB => Some(Hole)
    | LUB => Some(ty1)
    }
  | (Hole | Label(_), _) =>
    switch (j) {
    | GLB => Some(Hole)
    | LUB => Some(ty2)
    }
  | (Int, Int) => Some(ty1)
  | (Int, _) => None
  | (Float, Float) => Some(ty1)
  | (Float, _) => None
  | (Bool, Bool) => Some(ty1)
  | (Bool, _) => None
  | (Arrow(ty1, ty2), Arrow(ty1', ty2')) =>
    switch (join(j, ty1, ty1'), join(j, ty2, ty2')) {
    | (Some(ty1), Some(ty2)) => Some(Arrow(ty1, ty2))
    | _ => None
    }
  | (Arrow(_), _) => None
  | (Sum(ty1, ty2), Sum(ty1', ty2')) =>
    switch (join(j, ty1, ty1'), join(j, ty2, ty2')) {
    | (Some(ty1), Some(ty2)) => Some(Sum(ty1, ty2))
    | _ => None
    }
  | (Sum(_), _) => None
  | (Prod(tys1), Prod(tys2)) =>
    ListUtil.map2_opt(
      ((label1, ty1), (label2, ty2)) => {
        switch (label1, label2) {
        | (Some(l1), Some(l2)) when l1 == l2 =>
          Some((label1, Option.get(join(j, ty1, ty2))))
        | (None, None) => Some((None, Option.get(join(j, ty1, ty2))))
        | (Some(_), None)
        | (None, Some(_)) => None
        }
      },
      tys1,
      tys2,
    )
    |> Option.map(OptUtil.sequence)
    |> Option.join
    |> Option.map(joined_types => Prod(joined_types))
  | (Prod(_), _) => None
  | (List(ty), List(ty')) =>
    switch (join(j, ty, ty')) {
    | Some(ty) => Some(List(ty))
    | None => None
    }
  | (List(_), _) => None
  };

let join_all = (j: join, types: list(t)): option(t) => {
  switch (types) {
  | [] => None
  | [hd] => Some(hd)
  | [hd, ...tl] =>
    if (!consistent_all(types)) {
      None;
    } else {
      List.fold_left(
        (common_opt, ty) =>
          switch (common_opt) {
          | None => None
          | Some(common_ty) => join(j, common_ty, ty)
          },
        Some(hd),
        tl,
      );
    }
  };
};
