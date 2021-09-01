type cursor_term = CursorInfo.cursor_term;
type zoperand = CursorInfo_common.zoperand;

let extract_cursor_term = (CursorTag(cursor, tag): ZTag.t): cursor_term =>
  Tag(cursor, tag);

let cursor_info = (ctx: Contexts.t, ztag: ZTag.t): option(CursorInfo.t) =>
  Some(CursorInfo_common.mk(OnTag, ctx, extract_cursor_term(ztag)));

let get_zoperand = (ztag: ZTag.t): option(zoperand) => Some(ZTag(ztag));

let get_outer_zrules =
    (_: ZTag.t, outer_zrules: option(ZExp.zrules)): option(ZExp.zrules) => outer_zrules;