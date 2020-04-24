// TODO: compute actual layout size and use instead of t_of_layout
let rec all: 'annot. Doc.t('annot) => list(Layout.t('annot)) = {
  doc => {
    switch (doc.doc) {
    | Text(string) => [Layout.Text(string)]
    | Cat(d1, d2) =>
      let ls1 = all(d1);
      let ls2 = all(d2);
      List.concat(
        List.map(l1 => List.map(l2 => Layout.Cat(l1, l2), ls2), ls1),
      );
    | Linebreak => [Layout.Linebreak]
    | Align(d) => List.map(l => Layout.Align(l), all(d))
    | Annot(annot, d) => List.map(l => Layout.Annot(annot, l), all(d))
    | Fail => []
    | Choice(d1, d2) => all(d1) @ all(d2)
    };
  };
};

type m('a) = Doc.m('a);
type m'('a) = Doc.m'('a);
module Table = Hashtbl.Make(Doc.WidthPosKey);

// Note: This union is left biased
let m'_union: 'a. (m'('a), m'('a)) => m'('a) =
  (p1, p2) => {
    let cost_union = ((cost1, _) as t1, (cost2, _) as t2) =>
      if (cost1 <= cost2) {
        t1;
      } else {
        t2;
      };
    PosMap.union(cost_union, p1, p2);
  };

let rec layout_of_doc': 'annot. Doc.t('annot) => m(Layout.t('annot)) =
  (doc, ~width: int, ~pos: int) => {
    Obj.magic(snd(Lazy.force(memo_table), Obj.magic(doc), ~width, ~pos));
  }

and memo_table: Lazy.t((unit => unit, Doc.t(unit) => m(Layout.t(unit)))) =
  lazy((
    () => (),
    (d, ~width, ~pos) => {
      let key = (width, pos);
      switch (Doc.M.find_opt(d.mem, key)) {
      | Some(value) => value
      | None =>
        let value = layout_of_doc''(d, ~width, ~pos);
        Doc.M.add(d.mem, key, value);
        value;
      };
    },
  ))

and layout_of_doc'': Doc.t(unit) => m(Layout.t(unit)) =
  doc => {
    let g = (~width: int, ~pos: int): m'(Layout.t(unit)) => {
      // TODO: lift the switch(doc.doc) outside the lambda
      switch (doc.doc) {
      | Text(string) =>
        // TODO: cache text length in Text?
        let pos' = pos + Unicode.length(string);
        if (pos' > width) {
          PosMap.empty;
        } else {
          PosMap.singleton(pos', (0, Layout.Text(string)));
        };
      | Cat(d1, d2) =>
        let l1 = layout_of_doc'(d1, ~width, ~pos);
        PosMap.fold_left(
          (pos, z, (cost1, layout1)) => {
            let l2 = layout_of_doc'(d2, ~width, ~pos);
            let layouts =
              PosMap.map(
                ((cost2, layout2)) =>
                  (cost1 + cost2, Layout.Cat(layout1, layout2)),
                l2,
              );
            m'_union(z, layouts);
          },
          PosMap.empty,
          l1,
        );
      | Linebreak => PosMap.singleton(0, (1, Layout.Linebreak))
      | Align(d) =>
        let layout = layout_of_doc'(d, ~width=width - pos, ~pos=0);
        PosMap.mapk(
          (p, (c, l)) => (p + pos, (c, Layout.Align(l))),
          layout,
        );
      | Annot(annot, d) =>
        let layout = layout_of_doc'(d, ~width, ~pos);
        PosMap.map(((c, l)) => (c, Layout.Annot(annot, l)), layout);
      | Fail => PosMap.empty
      | Choice(d1, d2) =>
        let l1 = layout_of_doc'(d1, ~width, ~pos);
        let l2 = layout_of_doc'(d2, ~width, ~pos);
        m'_union(l1, l2);
      };
    };
    let table = Table.create(0);
    let h = (~width: int, ~pos: int): m'(Layout.t(unit)) => {
      let key = (width, pos);
      switch (Table.find_opt(table, key)) {
      | Some(value) => value
      | None =>
        let value = g(~width, ~pos);
        Table.add(table, key, value);
        value;
      };
    };
    h;
  };

let layout_of_doc =
    (doc: Doc.t('annot), ~width: int, ~pos: int): option(Layout.t('annot)) => {
  let rec minimum =
          ((pos, (cost, t)): (int, (int, option('a))))
          : (list((int, (int, 'a))) => option('a)) => {
    fun
    | [] => t
    | [(x_pos, (x_cost, x)), ...rest] =>
      // Prefer lowest cost, or if same cost, prefer ending at an earlier column
      // (Columns are unique by construction of PosMap.)
      if (x_cost < cost || x_cost == cost && x_pos < pos) {
        minimum((x_pos, (x_cost, Some(x))), rest);
      } else {
        minimum((pos, (cost, t)), rest);
      };
  };
  // TODO: use options instead of max_int
  // let start_time = Sys.time();
  let l =
    minimum((max_int, (max_int, None)), layout_of_doc'(doc, ~width, ~pos));
  // let end_time = Sys.time();
  /*
   Printf.printf(
     "layout_of_doc: %d \t%f\n",
     -1, //fst(Lazy.force(memo_table))##.size,
     //Memoize.WeakPoly.Table.length(fst(Lazy.force(memo_table))),
     1000.0 *. (end_time -. start_time),
   );
   */
  l;
};
