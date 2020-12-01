open Sexplib.Std;

module Memo = Core_kernel.Memo;

module MeasuredPosition = Pretty.MeasuredPosition;
module MeasuredLayout = Pretty.MeasuredLayout;

[@deriving sexp]
type filling_hole = (
  MetaVar.t,
  ZList.t(UHExp.t, UHExp.t) /* + constraints */,
);

[@deriving sexp]
type t = {
  edit_state: Statics.edit_state,
  width: int,
  start_col_of_vertical_movement: option(int),
  is_focused: bool,
  synthesizing: option(Synthesizing.t),
};

let mk = (~width: int, ~is_focused=false, edit_state: Statics.edit_state): t => {
  width,
  edit_state,
  start_col_of_vertical_movement: None,
  is_focused,
  synthesizing: None,
};

let put_start_col = (start_col, program) => {
  ...program,
  start_col_of_vertical_movement: Some(start_col),
};
let clear_start_col = program => {
  ...program,
  start_col_of_vertical_movement: None,
};

let focus = program => {...program, is_focused: true};
let blur = program => {...program, is_focused: false};

let put_edit_state = (edit_state, program) => {...program, edit_state};

let get_zexp = program => {
  let (ze, _, _) = program.edit_state;
  ze;
};

let erase = Memo.general(~cache_size_bound=1000, ZExp.erase);
let get_uhexp = program => program |> get_zexp |> erase;

let get_path = program => program |> get_zexp |> CursorPath_Exp.of_z;
let get_steps = program => {
  let (steps, _) = program |> get_path;
  steps;
};
let get_id_gen = program => {
  let (_, _, id_gen) = program.edit_state;
  id_gen;
};

exception MissingCursorInfo;
let cursor_info =
  Memo.general(
    ~cache_size_bound=1000,
    CursorInfo_Exp.syn_cursor_info(Contexts.empty),
  );
let get_cursor_info = (program: t) => {
  program
  |> get_zexp
  |> cursor_info
  |> OptUtil.get(() => raise(MissingCursorInfo));
};

exception DoesNotElaborate;
let expand =
  Memo.general(
    ~cache_size_bound=1000,
    Elaborator_Exp.syn_elab(Contexts.empty, Delta.empty),
  );
let get_expansion = (program: t): DHExp.t =>
  switch (program |> get_uhexp |> expand) {
  | DoesNotElaborate => raise(DoesNotElaborate)
  | Elaborates(d, _, _) => d
  };

exception InvalidInput;

let evaluate = Memo.general(~cache_size_bound=1000, Evaluator.evaluate);

let get_result = (program: t): (Result.t, AssertMap.t) =>
  //check if map is resetted here
  switch (AssertMap.empty |> evaluate(get_expansion(program))) {
  | (InvalidInput(_), _) => raise(InvalidInput)
  | (BoxedValue(d), assert_map) =>
    let (d_renumbered, hii) =
      Elaborator_Exp.renumber([], HoleInstanceInfo.empty, d);
    ((d_renumbered, hii, BoxedValue(d_renumbered)), assert_map);
  | (Indet(d), assert_map) =>
    let (d_renumbered, hii) =
      Elaborator_Exp.renumber([], HoleInstanceInfo.empty, d);
    ((d_renumbered, hii, Indet(d_renumbered)), assert_map);
  };

exception HoleNotFound;

let get_decoration_paths = (program: t): UHDecorationPaths.t => {
  let current_term =
    program.is_focused && Option.is_none(program.synthesizing)
      ? Some(get_path(program)) : None;
  let (err_holes, var_err_holes) =
    CursorPath_Exp.holes(get_uhexp(program), [], [])
    |> List.filter_map((CursorPath.{sort, steps}) =>
         switch (sort) {
         | TypHole => None
         | PatHole(_, shape)
         | ExpHole(_, shape) =>
           switch (shape) {
           | Empty => None
           | VarErr
           | TypeErr => Some((shape, steps))
           }
         }
       )
    |> List.partition(
         fun
         | (CursorPath.TypeErr, _) => true
         | (_var_err, _) => false,
       )
    |> TupleUtil.map2(List.map(snd));
  let var_uses =
    switch (get_cursor_info(program)) {
    | {uses: Some(uses), _} => uses
    | _ => []
    };
  let filled_holes = Synthesizing.(F(HoleMap.empty));
  let synthesizing = program.synthesizing;
  {
    current_term,
    err_holes,
    var_uses,
    var_err_holes,
    filled_holes,
    synthesizing,
  };
};

exception FailedAction;
exception CursorEscaped;
let perform_edit_action = (a, program) => {
  let edit_state = program.edit_state;
  switch (Action_Exp.syn_perform(Contexts.empty, a, edit_state)) {
  | Failed => raise(FailedAction)
  | CursorEscaped(_) => raise(CursorEscaped)
  | Succeeded(new_edit_state) =>
    let (ze, ty, id_gen) = new_edit_state;
    let new_edit_state =
      if (UHExp.is_complete(ZExp.erase(ze), false)) {
        (ze, ty, IDGen.init_hole(id_gen));
      } else {
        (ze, ty, id_gen);
      };
    program |> put_edit_state(new_edit_state);
  };
};

let move_to_hole = (u, program) => {
  let (ze, _, _) = program.edit_state;
  let holes = CursorPath_Exp.holes(ZExp.erase(ze), [], []);
  switch (CursorPath_common.steps_to_hole(holes, u)) {
  | None => raise(HoleNotFound)
  | Some(hole_steps) =>
    let e = ZExp.erase(ze);
    switch (CursorPath_Exp.of_steps(hole_steps, e)) {
    | None => raise(HoleNotFound)
    | Some(hole_path) => Action.MoveTo(hole_path)
    };
  };
};

let move_to_case_branch = (steps_to_case, branch_index): Action.t => {
  let steps_to_branch = steps_to_case @ [1 + branch_index];
  Action.MoveTo((steps_to_branch, OnDelim(1, After)));
};

let get_doc = (~measure_program_get_doc: bool, ~memoize_doc: bool, program) => {
  TimeUtil.measure_time("Program.get_doc", measure_program_get_doc, () => {
    Lazy.force(
      UHDoc_Exp.mk,
      ~memoize=memoize_doc,
      ~enforce_inline=false,
      get_uhexp(program),
    )
  });
};

let get_layout =
    (
      ~measure_program_get_doc: bool,
      ~measure_layoutOfDoc_layout_of_doc: bool,
      ~memoize_doc: bool,
      program,
    ) => {
  let width = program.width;
  let doc = get_doc(~measure_program_get_doc, ~memoize_doc, program);
  TimeUtil.measure_time(
    "LayoutOfDoc.layout_of_doc", measure_layoutOfDoc_layout_of_doc, () =>
    Pretty.LayoutOfDoc.layout_of_doc(~width, ~pos=0, doc)
  )
  |> OptUtil.get(() => failwith("unimplemented: layout failure"));
};

let get_measured_layout =
    (
      ~measure_program_get_doc: bool,
      ~measure_layoutOfDoc_layout_of_doc: bool,
      ~memoize_doc: bool,
      program,
    )
    : UHMeasuredLayout.t => {
  program
  |> get_layout(
       ~measure_program_get_doc,
       ~measure_layoutOfDoc_layout_of_doc,
       ~memoize_doc,
     )
  |> UHMeasuredLayout.mk;
};

let get_caret_position =
    (
      ~measure_program_get_doc: bool,
      ~measure_layoutOfDoc_layout_of_doc: bool,
      ~memoize_doc: bool,
      program,
    )
    : MeasuredPosition.t => {
  let m =
    get_measured_layout(
      ~measure_program_get_doc,
      ~measure_layoutOfDoc_layout_of_doc,
      ~memoize_doc,
      program,
    );
  let path = get_path(program);
  UHMeasuredLayout.caret_position_of_path(path, m)
  |> OptUtil.get(() => failwith("could not find caret"));
};

let move_via_click =
    (
      ~measure_program_get_doc: bool,
      ~measure_layoutOfDoc_layout_of_doc: bool,
      ~memoize_doc: bool,
      target: MeasuredPosition.t,
      program,
    )
    : (t, Action.t) => {
  let m =
    get_measured_layout(
      ~measure_program_get_doc,
      ~measure_layoutOfDoc_layout_of_doc,
      ~memoize_doc,
      program,
    );
  let path =
    UHMeasuredLayout.nearest_path_within_row(target, m)
    |> OptUtil.get(() => failwith("row with no caret positions"))
    |> fst
    |> CursorPath_common.rev;
  let new_program =
    program |> focus |> clear_start_col |> perform_edit_action(MoveTo(path));
  (new_program, MoveTo(path));
};

let move_via_key =
    (
      ~measure_program_get_doc: bool,
      ~measure_layoutOfDoc_layout_of_doc: bool,
      ~memoize_doc: bool,
      move_key: MoveKey.t,
      program,
    )
    : (t, Action.t) => {
  let caret_position =
    get_caret_position(
      ~measure_program_get_doc,
      ~measure_layoutOfDoc_layout_of_doc,
      ~memoize_doc,
      program,
    );
  let m =
    get_measured_layout(
      ~measure_program_get_doc,
      ~measure_layoutOfDoc_layout_of_doc,
      ~memoize_doc,
      program,
    );
  let (from_col, put_col_on_start) =
    switch (program.start_col_of_vertical_movement) {
    | None =>
      let col = caret_position.col;
      (col, put_start_col(col));
    | Some(col) => (col, (p => p))
    };
  let (new_z, update_start_col) =
    switch (move_key) {
    | ArrowUp =>
      let up_target =
        MeasuredPosition.{row: caret_position.row - 1, col: from_col};
      (
        UHMeasuredLayout.nearest_path_within_row(up_target, m),
        put_col_on_start,
      );
    | ArrowDown =>
      let down_target =
        MeasuredPosition.{row: caret_position.row + 1, col: from_col};
      (
        UHMeasuredLayout.nearest_path_within_row(down_target, m),
        put_col_on_start,
      );
    | ArrowLeft => (
        switch (UHMeasuredLayout.prev_path_within_row(caret_position, m)) {
        | Some(_) as found => found
        | None =>
          caret_position.row > 0
            ? UHMeasuredLayout.last_path_in_row(caret_position.row - 1, m)
            : None
        },
        clear_start_col,
      )
    | ArrowRight => (
        switch (UHMeasuredLayout.next_path_within_row(caret_position, m)) {
        | Some(_) as found => found
        | None =>
          caret_position.row < MeasuredLayout.height(m) - 1
            ? UHMeasuredLayout.first_path_in_row(caret_position.row + 1, m)
            : None
        },
        clear_start_col,
      )
    | Home => (
        UHMeasuredLayout.first_path_in_row(caret_position.row, m),
        clear_start_col,
      )
    | End => (
        UHMeasuredLayout.last_path_in_row(caret_position.row, m),
        clear_start_col,
      )
    };

  switch (new_z) {
  | None => raise(CursorEscaped)
  | Some((rev_path, _)) =>
    let path = CursorPath_common.rev(rev_path);
    let new_program =
      program |> update_start_col |> perform_edit_action(MoveTo(path));
    (new_program, MoveTo(path));
  };
};

let cursor_on_exp_hole_ =
  Memo.general(~cache_size_bound=1000, ZExp.cursor_on_EmptyHole);
let cursor_on_exp_hole = program => program |> get_zexp |> cursor_on_exp_hole_;

let begin_synthesizing = (u, program) => {
  ...program,
  synthesizing: Synthesizing.mk(u, get_uhexp(program)),
};

let try_synth_update = (f: Synthesizing.t => option(Synthesizing.t), program) =>
  switch (program.synthesizing) {
  | None => program
  | Some(synth) =>
    switch (f(synth)) {
    | None => program
    | Some(_) as synthesizing => {...program, synthesizing}
    }
  };

let scroll_synthesized_selection = up =>
  try_synth_update(Synthesizing.scroll(up));

let prev_synthesis_hole = program =>
  try_synth_update(
    Synthesizing.move_to_prev_hole(get_uhexp(program)),
    program,
  );
let next_synthesis_hole = program =>
  try_synth_update(
    Synthesizing.move_to_next_hole(get_uhexp(program)),
    program,
  );

let step_in_synthesized = program =>
  try_synth_update(Synthesizing.step_in(get_uhexp(program)), program);
let step_out_synthesized = program =>
  try_synth_update(Synthesizing.step_out(get_uhexp(program)), program);

let accept_synthesized = program =>
  switch (program.synthesizing) {
  | None => program
  | Some(syn) =>
    let e = Synthesizing.accept(get_uhexp(program), syn);
    let id_gen = get_id_gen(program);
    let (e, ty, id_gen) =
      Statics_Exp.syn_fix_holes(
        Contexts.empty,
        id_gen,
        ~renumber_empty_holes=true,
        e,
      );
    let edit_state = (ZExp.place_before(e), ty, id_gen);
    {...program, edit_state, is_focused: false, synthesizing: None};
  };
