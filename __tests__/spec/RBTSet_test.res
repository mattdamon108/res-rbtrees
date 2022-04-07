open Zora

let testEqual = (t, name, lhs, rhs) =>
  t->test(name, t => {
    t->equal(lhs, rhs, name)

    done()
  })

module KeyS = {
  type t = int
  let compare = Pervasives.compare
}

module Set = RBTSet.Make(KeyS)

let empty = Set.empty
let m1 = empty->Set.add(1)

zoraBlock("-- isEmpty --", t => {
  t->testEqual("* empty", empty->Set.isEmpty, true)
  t->testEqual("* not empty", m1->Set.isEmpty, false)
})

zoraBlock("-- add & mem --", t => {
  let m2 = m1->Set.add(2)
  let m3 = m2->Set.add(3)
  t->testEqual("* mem 2", m3->Set.mem(2), true)
})
