// Generated by BUCKLESCRIPT, PLEASE EDIT WITH CARE
'use strict';


var id = {
  contents: 100
};

function getId(param) {
  var i = id.contents;
  id.contents = i + 1 | 0;
  return i;
}

exports.id = id;
exports.getId = getId;
/* No side effect */