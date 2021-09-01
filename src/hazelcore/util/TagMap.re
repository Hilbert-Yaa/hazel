open OptUtil.Syntax;
open Sexplib.Std;

[@deriving sexp]
type key = UHTag.t;

[@deriving sexp]
type t('a) = list((key, 'a));

let empty: t('a) = [];

let singleton = (tag: key, value: 'a): t('a) => [(tag, value)];

let rec add = (tag: key, value: 'a, map: t('a)): t('a) =>
  switch (map) {
  | [] => [(tag, value)]
  | [(tag', value') as head, ...tail] =>
    if (UHTag.eq(tag, tag')) {
      if (value === value') {
        map;
      } else {
        [(tag, value), ...tail];
      };
    } else {
      [head, ...add(tag, value, tail)];
    }
  };

let bindings = (map: t('a)): list((UHTag.t, 'a)) => map;

let of_list = (bindings: list((UHTag.t, 'a))): t('a) => bindings;

/* compares tags only */
let compare_bindings =
    ((tag1, _): (UHTag.t, 'a), (tag2, _): (UHTag.t, 'a)): int =>
  UHTag.compare(tag1, tag2);

let equal_tags = (map1: t('a), map2: t('a)): bool => {
  let tags1 = map1 |> List.map(fst);
  let tags2 = map2 |> List.map(fst);
  tags1 === tags2
  || List.fast_sort(UHTag.compare, tags1)
  == List.fast_sort(UHTag.compare, tags2);
};

let equal_bindings =
    (
      val_equal: ('a, 'a) => bool,
      (tag1: UHTag.t, val1: 'a),
      (tag2: UHTag.t, val2: 'a),
    )
    : bool =>
  UHTag.eq(tag1, tag2) && val_equal(val1, val2);

let equal = (val_equal: ('a, 'a) => bool, map1: t('a), map2: t('a)): bool => {
  map1 === map2
  || {
    let map1 = List.fast_sort(compare_bindings, map1);
    let map2 = List.fast_sort(compare_bindings, map2);
    ListUtil.equal(equal_bindings(val_equal), map1, map2);
  };
};

/* sorts on tags only */
let sort = (map: t('a)): t('a) => {
  List.fast_sort(compare_bindings, map);
};

let find_opt = (key: key, map: t('a)): option('a) => {
  let+ binding = List.find_opt(((k, _)) => UHTag.eq(key, k), map);
  snd(binding);
};

let map = (f: 'a => 'b, m: t('a)): t('b) => {
  let (keys, vals) = List.split(m);
  let vals = List.map(f, vals);
  List.combine(keys, vals);
};