// Generated by BUCKLESCRIPT, PLEASE EDIT WITH CARE
'use strict';

var List = require("bs-platform/lib/js/list.js");
var Pervasives = require("bs-platform/lib/js/pervasives.js");
var Guesser$MyNewProject = require("./Guesser.bs.js");
var Refiner$MyNewProject = require("./Refiner.bs.js");
var Brancher$MyNewProject = require("./Brancher.bs.js");
var Unevaluator$MyNewProject = require("./unevaluator.bs.js");

function updateHoleContext_h(delta, gs) {
  if (!gs) {
    return delta;
  }
  var match = gs[0];
  var xs = updateHoleContext_h(delta, gs[1]);
  return /* :: */[
          /* tuple */[
            match[1],
            /* tuple */[
              match[0],
              match[2]
            ]
          ],
          xs
        ];
}

function updateHoleContext(delta, h, gs) {
  return List.filter((function (param) {
                  return h !== param[0];
                }))(updateHoleContext_h(delta, gs));
}

function updateUnfilledHoles(gs) {
  if (!gs) {
    return /* [] */0;
  }
  var match = gs[0];
  return /* :: */[
          /* tuple */[
            match[1],
            match[3]
          ],
          updateUnfilledHoles(gs[1])
        ];
}

function optionPred(x) {
  return x !== undefined;
}

function guessAndCheck_h(delta, gamma, f, typ, exs, _i) {
  while(true) {
    var i = _i;
    if (i > 8) {
      return ;
    }
    var es = Guesser$MyNewProject.guess(delta, gamma, typ, i);
    var checked = List.filter((function (e) {
              return optionPred(Unevaluator$MyNewProject.constrainExp(delta, f, e, exs));
            }))(es);
    if (checked) {
      return checked[0];
    }
    _i = i + 1 | 0;
    continue ;
  };
}

function guessAndCheck(delta, gamma, f, typ, exs) {
  Guesser$MyNewProject.resetMemo(undefined);
  return guessAndCheck_h(delta, gamma, f, typ, exs, 1);
}

function allBranchesFound(_xs) {
  while(true) {
    var xs = _xs;
    if (!xs) {
      return true;
    }
    if (xs[0] === undefined) {
      return false;
    }
    _xs = xs[1];
    continue ;
  };
}

function guessAndOrBranch(delta, holeFillings, gamma, h, typ, exs, depth) {
  var g = guessAndCheck(delta, gamma, holeFillings, typ, exs);
  if (g !== undefined) {
    var f_000 = /* tuple */[
      h,
      g
    ];
    var f = /* :: */[
      f_000,
      holeFillings
    ];
    var delta$prime = List.filter((function (param) {
              return h !== param[0];
            }))(delta);
    var k = /* tuple */[
      /* [] */0,
      f
    ];
    return /* tuple */[
            depth,
            /* :: */[
              /* tuple */[
                k,
                delta$prime
              ],
              /* [] */0
            ]
          ];
  }
  if (depth > 3) {
    return ;
  }
  var bs = List.map((function (param) {
          var goals = param[1];
          var f_000 = /* tuple */[
            h,
            param[0]
          ];
          var f = /* :: */[
            f_000,
            holeFillings
          ];
          var u = List.map((function (param) {
                  return /* tuple */[
                          param[1],
                          param[3]
                        ];
                }), goals);
          var delta$prime = List.filter((function (param) {
                    return h !== param[0];
                  }))(delta);
          var delta$prime$1 = Pervasives.$at(List.map((function (param) {
                      return /* tuple */[
                              param[1],
                              /* tuple */[
                                param[0],
                                param[2]
                              ]
                            ];
                    }), goals), delta$prime);
          return /* tuple */[
                  /* tuple */[
                    u,
                    f
                  ],
                  delta$prime$1
                ];
        }), Brancher$MyNewProject.branch(delta, gamma, holeFillings, typ, exs));
  return /* tuple */[
          depth + 1 | 0,
          bs
        ];
}

function fill_h(delta, holeFillings, gamma, h, typ, exs, depth) {
  if (!Refiner$MyNewProject.refinable(typ, exs)) {
    return guessAndOrBranch(delta, holeFillings, gamma, h, typ, exs, depth);
  }
  var match = Refiner$MyNewProject.refine(gamma, typ, exs);
  if (match === undefined) {
    return guessAndOrBranch(delta, holeFillings, gamma, h, typ, exs, depth);
  }
  var gs = match[1];
  var f_000 = /* tuple */[
    h,
    match[0]
  ];
  var f = /* :: */[
    f_000,
    holeFillings
  ];
  var delta$prime = updateHoleContext(delta, h, gs);
  var u = updateUnfilledHoles(gs);
  var k = /* tuple */[
    u,
    f
  ];
  return /* tuple */[
          depth,
          /* :: */[
            /* tuple */[
              k,
              delta$prime
            ],
            /* [] */0
          ]
        ];
}

function fill(delta, holeFillings, gamma, h, typ, exs, depth) {
  var match = fill_h(delta, holeFillings, gamma, h, typ, exs, depth);
  if (match !== undefined) {
    return /* tuple */[
            match[0],
            match[1]
          ];
  }
  
}

exports.updateHoleContext_h = updateHoleContext_h;
exports.updateHoleContext = updateHoleContext;
exports.updateUnfilledHoles = updateUnfilledHoles;
exports.optionPred = optionPred;
exports.guessAndCheck_h = guessAndCheck_h;
exports.guessAndCheck = guessAndCheck;
exports.allBranchesFound = allBranchesFound;
exports.fill = fill;
exports.fill_h = fill_h;
exports.guessAndOrBranch = guessAndOrBranch;
/* No side effect */