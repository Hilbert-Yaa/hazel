open Sexplib.Std;

[@deriving sexp]
type varexp =
  option(
    (
      Var.t,
      // steps of binding site
      CursorPath_common.steps,
      // index of current use
      int,
      // other uses
      UsageAnalysis.uses_list,
    ),
  );

[@deriving sexp]
type join_of_branches =
  | NoBranches
  // steps to the case
  | InconsistentBranchTys(list(HTyp.t), CursorPath_common.steps)
  | JoinTy(HTyp.t);

[@deriving sexp]
type typed =
  // cursor is on a lambda with an argument type annotation
  /* cursor in analytic position */
  | AnaAnnotatedLambda(HTyp.t, HTyp.t)
  // cursor is on a type inconsistent expression
  | AnaTypeInconsistent(HTyp.t, HTyp.t, varexp)
  // cursor is on a tuple of the wrong length
  | AnaWrongLength
      // expected length
      (
        int,
        // got length
        int,
        // expected type
        HTyp.t,
      )
  // cursor is on a free variable
  | AnaFree(HTyp.t)
  // cursor is on a keyword
  | AnaKeyword(HTyp.t, ExpandingKeyword.t)
  // none of the above and didn't go through subsumption
  | Analyzed(HTyp.t, varexp)
  // none of the above and went through subsumption
  | AnaSubsumed(HTyp.t, HTyp.t)
  /* cursor in synthetic position */
  // cursor is on the function position of an ap,
  // and that expression does not synthesize a type
  // with a matched arrow type
  | SynErrorArrow
      // expected
      (
        HTyp.t,
        // got
        HTyp.t,
        varexp,
      )
  // cursor is on the function position of an ap,
  // and that expression does synthesize a type
  // with a matched arrow type
  | SynMatchingArrow(HTyp.t, HTyp.t, varexp)
  // cursor is on a free variable in the function
  // position of an ap
  | SynFreeArrow(HTyp.t)
  // cursor is on a keyword in the function position of an ap
  | SynKeywordArrow(HTyp.t, ExpandingKeyword.t)
  // none of the above, cursor is on a free variable
  | SynFree
  // cursor is on a keyword
  | SynKeyword(ExpandingKeyword.t)
  // cursor is on the clause of a case
  | SynBranchClause
      // lub of other branches
      (
        join_of_branches,
        // info for the clause
        typed,
        // index of the branch
        int,
      )
  // cursor is on a case with branches of inconsistent types
  // keep track of steps to form that contains the branches
  | SynInconsistentBranches(list(HTyp.t), CursorPath_common.steps)
  // none of the above
  | Synthesized(HTyp.t, varexp)
  /* cursor in analytic pattern position */
  // cursor is on a type inconsistent pattern
  | PatAnaTypeInconsistent(HTyp.t, HTyp.t)
  // cursor is on a tuple pattern of the wrong length
  | PatAnaWrongLength
      // expected length
      (
        int,
        // got length
        int,
        // expected type
        HTyp.t,
      )
  // cursor is on a keyword
  | PatAnaKeyword(HTyp.t, ExpandingKeyword.t)
  // cursor is on a variable with duplicated name
  | PatAnaDuplicate(HTyp.t, Var.t)
  // cursor is on a variable bindint site and not in var hole
  | PatAnaVar(
      HTyp.t,
      Var.t,
      // shadowing
      bool,
      // variable warning
      VarWarnStatus.t,
      // number of uses
      UsageAnalysis.uses_list,
      // number of recursive uses
      UsageAnalysis.uses_list,
    )
  // none of the above and didn't go through subsumption
  | PatAnalyzed(HTyp.t)
  // none of the above and went through subsumption
  | PatAnaSubsumed(HTyp.t, HTyp.t)
  /* cursor in synthetic pattern position */
  // cursor is on a keyword
  | PatSynKeyword(ExpandingKeyword.t)
  // cursor is on a variable with duplicated name
  | PatSynDuplicate(Var.t)
  // cursor is on a variable and not in var hole
  | PatSynVar(
      HTyp.t,
      Var.t,
      // shadowing
      bool,
      // variable warning
      VarWarnStatus.t,
      // total variables uses
      UsageAnalysis.uses_list,
      // recursive variable uses
      UsageAnalysis.uses_list,
    )
  | PatSynthesized(HTyp.t)
  /* cursor in type position */
  | OnType
  /* (we will have a richer structure here later)*/
  | OnLine
  | OnRule;

[@deriving sexp]
type cursor_term =
  | Exp(CursorPosition.t, UHExp.operand)
  | Pat(CursorPosition.t, UHPat.operand)
  | Typ(CursorPosition.t, UHTyp.operand)
  | ExpOp(CursorPosition.t, UHExp.operator)
  | PatOp(CursorPosition.t, UHPat.operator)
  | TypOp(CursorPosition.t, UHTyp.operator)
  | Line(CursorPosition.t, UHExp.line)
  | Rule(CursorPosition.t, UHExp.rule);

// TODO refactor into variants
// based on term sort and shape
//[@deriving sexp]
type t = {
  cursor_term,
  typed,
  ctx: Contexts.t,
};

type zoperand =
  | ZExp(ZExp.zoperand)
  | ZTyp(ZTyp.zoperand)
  | ZPat(ZPat.zoperand);

let cursor_term_is_editable = (cursor_term: cursor_term): bool => {
  switch (cursor_term) {
  | Exp(_, exp) =>
    switch (exp) {
    | EmptyHole(_)
    | Var(_, _, _)
    | IntLit(_, _)
    | FloatLit(_, _)
    | BoolLit(_, _) => true
    | ApPalette(_, _, _, _) => failwith("ApPalette is not implemented")
    | _ => false
    }
  | Pat(_, pat) =>
    switch (pat) {
    | EmptyHole(_)
    | Wild(_)
    | Var(_, _, _, _)
    | IntLit(_, _)
    | FloatLit(_, _)
    | BoolLit(_, _) => true
    | _ => false
    }
  | Typ(_, _)
  | ExpOp(_, _)
  | PatOp(_, _)
  | TypOp(_, _) => false
  | Line(_, line) =>
    switch (line) {
    | EmptyLine => true
    | LetLine(_, _, _)
    | ExpLine(_) => false
    }
  | Rule(_, _) => false
  };
};

let is_empty_hole = (cursor_term: cursor_term): bool => {
  switch (cursor_term) {
  | Exp(_, EmptyHole(_)) => true
  | Exp(_, _) => false
  | Pat(_, EmptyHole(_)) => true
  | Pat(_, _) => false
  | Typ(_, Hole) => true
  | Typ(_, _) => false
  | ExpOp(_, _)
  | PatOp(_, _)
  | TypOp(_, _)
  | Line(_, _)
  | Rule(_, _) => false
  };
};

let is_empty_line = (cursor_term): bool => {
  switch (cursor_term) {
  | Line(_, EmptyLine) => true
  | Line(_, _) => false
  | Exp(_, _)
  | Pat(_, _)
  | Typ(_, _)
  | ExpOp(_, _)
  | PatOp(_, _)
  | TypOp(_, _)
  | Rule(_, _) => false
  };
};

let mk = (typed, ctx, cursor_term) => {typed, ctx, cursor_term};

let get_ctx = ci => ci.ctx;

/*
 * there are cases we can't determine where to find the uses of a variable
 * immediately after we see its binding site.
 * in this case, we will return a deferrable('t) and go up the tree
 * until we could find uses and feed it to (uses_list => 't).
 */

type deferrable('t) =
  | CursorNotOnDeferred('t)
  | CursorOnDeferredVarPat
      // non-recursive uses
      (
        (
          UsageAnalysis.uses_list,
          // recursive uses
          UsageAnalysis.uses_list
        ) =>
        't,
        Var.t,
      )
  | CursorOnDeferredVarExp(
      UsageAnalysis.uses_list => 't,
      // steps of binding site
      CursorPath_common.steps,
      Var.t,
    );
