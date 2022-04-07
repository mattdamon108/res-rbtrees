open Zora

let testEqual = (t, name, lhs, rhs) =>
  t->test(name, t => {
    t->equal(lhs, rhs, name)

    done()
  })

module KeyM = {
  type t = string
  let compare = String.compare
}

module Map = RBTMap.Make(KeyM)

let empty = Map.empty
let m1 = empty->Map.add("ReScript", "awesome")

zoraBlock("-- isEmpty --", t => {
  t->testEqual("* empty", empty->Map.isEmpty, true)
  t->testEqual("* not empty", m1->Map.isEmpty, false)
})

zoraBlock("-- add & find --", t => {
  let m2 = m1->Map.add("OCaml", "super awesome")
  let m3 = m2->Map.add("Reason", "deprecated")
  t->testEqual("* OCaml should be super awesome ", m3->Map.find("OCaml"), "super awesome")
})
