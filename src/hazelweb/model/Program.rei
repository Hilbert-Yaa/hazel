/**
 * A Hazel program ready for user interaction.
 * Contains, in addition to {!type:Statics_common.edit_state},
 * user interface state such as the current width of
 * the editor, whether the editor is focused, etc.
 */
[@deriving sexp]
type t;

let mk: (~width: int, ~is_focused: bool=?, Statics_common.edit_state) => t;

let get_width: t => int;

let is_focused: t => bool;
let focus: t => t;
let blur: t => t;

let get_edit_state: t => Statics_common.edit_state;
let put_edit_state: (Statics_common.edit_state, t) => t;

let get_zexp: t => ZExp.t;
let get_uhexp: t => UHExp.t;

let get_path: t => CursorPath_common.t;
let get_steps: t => CursorPath_common.steps;

let get_u_gen: t => MetaVarGen.t;

exception MissingCursorInfo;
let get_cursor_info: t => CursorInfo_common.t;

exception DoesNotElaborate;
let get_expansion: t => DHExp.t;

exception InvalidInput;
let get_result: t => Result.t;

exception FailedAction;
exception CursorEscaped;
let perform_edit_action: (Action_common.t, t) => t;
let move_via_key:
  (
    ~measure_program_get_doc: bool,
    ~measure_layoutOfDoc_layout_of_doc: bool,
    ~memoize_doc: bool,
    JSUtil.MoveKey.t,
    t
  ) =>
  (t, Action_common.t);
let move_via_click:
  (
    ~measure_program_get_doc: bool,
    ~measure_layoutOfDoc_layout_of_doc: bool,
    ~memoize_doc: bool,
    (CursorMap.Row.t, CursorMap.Col.t),
    t
  ) =>
  (t, Action_common.t);

exception HoleNotFound;
let move_to_hole: (MetaVar.t, t) => t;
let move_to_case_branch:
  (CursorPath_common.steps, int, t) => (t, Action_common.t);

let get_doc:
  (~measure_program_get_doc: bool, ~memoize_doc: bool, t) => UHDoc_common.t;
let get_layout:
  (
    ~measure_program_get_doc: bool,
    ~measure_layoutOfDoc_layout_of_doc: bool,
    ~memoize_doc: bool,
    t
  ) =>
  UHLayout.t;
let get_decorated_layout:
  (
    ~measure_program_get_doc: bool,
    ~measure_layoutOfDoc_layout_of_doc: bool,
    ~memoize_doc: bool,
    t
  ) =>
  UHLayout.t;
let get_cursor_map:
  (
    ~measure_program_get_doc: bool,
    ~measure_layoutOfDoc_layout_of_doc: bool,
    ~memoize_doc: bool,
    t
  ) =>
  CursorMap.t;
let get_cursor_map_z:
  (
    ~measure_program_get_doc: bool,
    ~measure_layoutOfDoc_layout_of_doc: bool,
    ~memoize_doc: bool,
    t
  ) =>
  (CursorMap.t, CursorMap.binding);

let cursor_on_exp_hole: t => option(MetaVar.t);
