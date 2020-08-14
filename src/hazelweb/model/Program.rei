/**
 * A Hazel program ready for user interaction.
 * Contains, in addition to `Statics_common.edit_state`,
 * user interface state such as the current width of
 * the editor, whether the editor is focused, etc.
 */
[@deriving sexp]
type t =
  pri {
    edit_state: Statics_common.edit_state,
    width: int,
    start_col_of_vertical_movement: option(int),
    is_focused: bool,
  };

let mk: (~width: int, ~is_focused: bool=?, Statics_common.edit_state) => t;

let focus: t => t;
let blur: t => t;

let get_zexp: t => ZExp.t;
let get_uhexp: t => UHExp.t;

let get_steps: t => CursorPath_common.steps;

/**
 * Raised when `CursorInfo_Exp.syn_cursor_info` returns None
 * (indicates a bug, either in that function or in Action
 * because Action needs to return a well-typed edit state)
 */
exception MissingCursorInfo;
let get_cursor_info: t => CursorInfo_common.t;

let get_decoration_paths: t => UHDecorationPaths.t;

/**
 * Raised when edit state does not elaborate
 * (indicates a bug, either in that function or in Action
 * because Action needs to return a well-typed edit state) */
exception DoesNotElaborate;
let get_expansion: t => DHExp.t;

/**
 * Raised when evaluation fails with the InvalidInput output
 * (indicates a bug, either in that function or in Action
 * because Action needs to return a well-typed edit state)
 */
exception InvalidInput;
let get_result: t => Result.t;

/**
 * Raised when an attempted edit action does not succeed
 */
exception FailedAction;
exception CursorEscaped;
let perform_edit_action: (Action_common.t, t) => t;
let move_via_key:
  (
    ~measure_program_get_doc: bool,
    ~measure_layoutOfDoc_layout_of_doc: bool,
    ~memoize_doc: bool,
    MoveKey.t,
    t
  ) =>
  (t, Action_common.t);
let move_via_click:
  (
    ~measure_program_get_doc: bool,
    ~measure_layoutOfDoc_layout_of_doc: bool,
    ~memoize_doc: bool,
    Pretty.MeasuredPosition.t,
    t
  ) =>
  (t, Action_common.t);

exception HoleNotFound;
let move_to_hole: (MetaVar.t, t) => t;

/**
 * `select_case_branch(steps, n, program)` moves the cursor to the `n`th branch
 * in case expression found at `steps` (when the user clicks on a branch type
 * in the error message for a case expression with inconsistent branches)
 */
let move_to_case_branch:
  (CursorPath_common.steps, int, t) => (t, Action_common.t);

let get_layout:
  (
    ~measure_program_get_doc: bool,
    ~measure_layoutOfDoc_layout_of_doc: bool,
    ~memoize_doc: bool,
    t
  ) =>
  UHLayout.t;

let cursor_on_exp_hole: t => option(MetaVar.t);

let get_caret_position:
  (
    ~measure_program_get_doc: bool,
    ~measure_layoutOfDoc_layout_of_doc: bool,
    ~memoize_doc: bool,
    t
  ) =>
  Pretty.MeasuredPosition.t;
