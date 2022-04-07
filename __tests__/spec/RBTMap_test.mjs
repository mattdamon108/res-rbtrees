// Generated by ReScript, PLEASE EDIT WITH CARE

import * as Zora from "@dusty-phillips/rescript-zora/src/Zora.mjs";
import * as Zora$1 from "zora";
import * as Curry from "@rescript/std/lib/es6/curry.js";
import * as RBTMap from "../../src/RBTMap.mjs";
import * as $$String from "@rescript/std/lib/es6/string.js";

function testEqual(t, name, lhs, rhs) {
  t.test(name, (function (t) {
          t.equal(lhs, rhs, name);
          return Zora.done(undefined);
        }));
  
}

var Key = {
  compare: $$String.compare
};

var $$Map = RBTMap.Make(Key);

var empty = $$Map.empty;

var m1 = Curry._3($$Map.add, "ReScript", "awesome", empty);

Zora$1.test("-- isEmpty --", (function (t) {
        testEqual(t, "* empty", Curry._1($$Map.isEmpty, empty), true);
        return testEqual(t, "* not empty", Curry._1($$Map.isEmpty, m1), false);
      }));

Zora$1.test("-- add & find --", (function (t) {
        var m2 = Curry._3($$Map.add, "OCaml", "super awesome", m1);
        var m3 = Curry._3($$Map.add, "Reason", "deprecated", m2);
        return testEqual(t, "* OCaml should be super awesome ", Curry._2($$Map.find, "OCaml", m3), "super awesome");
      }));

export {
  testEqual ,
  Key ,
  $$Map ,
  empty ,
  m1 ,
  
}
/* Map Not a pure module */