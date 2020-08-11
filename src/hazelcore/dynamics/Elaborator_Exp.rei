/* closed substitution [d1/x]d2*/
let subst_var: (DHExp.t, Var.t, DHExp.t) => DHExp.t;

let subst: (Environment.t, DHExp.t) => DHExp.t;

type match_result =
  | Matches(Environment.t)
  | DoesNotMatch
  | Indet;

let matches: (DHPat.t, DHExp.t) => match_result;

type elab_result_lines =
  | LinesExpand(DHExp.t => DHExp.t, Contexts.t, Delta.t)
  | LinesDoNotExpand;

module ElaborationResult: {
  type t =
    | Elaborates(DHExp.t, HTyp.t, Delta.t)
    | DoesNotElaborate;

  let to_option: t => option((DHExp.t, HTyp.t, Delta.t));

  let from_option: option((DHExp.t, HTyp.t, Delta.t)) => t;

  let bind: (t, ~f: ((DHExp.t, HTyp.t, Delta.t)) => t) => t;
};

module Let_syntax = ElaborationResult;

let id_env: VarCtx.t => Environment.t;

let syn_elab: (Contexts.t, Delta.t, UHExp.t) => ElaborationResult.t;

let ana_elab: (Contexts.t, Delta.t, UHExp.t, HTyp.t) => ElaborationResult.t;

let renumber:
  (InstancePath.t, HoleInstanceInfo.t, DHExp.t) =>
  (DHExp.t, HoleInstanceInfo.t);
