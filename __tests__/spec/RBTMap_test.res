open Zora

let testEqual = (t, name, lhs, rhs) =>
  t->test(name, t => {
    t->equal(lhs, rhs, name)

    done()
  })

module Key = {
  type t = string
  let compare = String.compare
}

module Map = RBTMap.Make(Key)

let empty = Map.empty
let m1 = Map.add("ReScript", "awesome", empty)

zoraBlock("-- isEmpty --", t => {
  t->testEqual("* empty", empty->Map.isEmpty, true)
  t->testEqual("* not empty", m1->Map.isEmpty, false)
})

zoraBlock("-- add & find --", t => {
  let m2 = Map.add("OCaml", "super awesome", m1)
  let m3 = Map.add("Reason", "deprecated", m2)
  t->testEqual("* OCaml should be super awesome ", Map.find("OCaml", m3), "super awesome")
})
