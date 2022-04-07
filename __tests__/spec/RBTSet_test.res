open Zora

let testEqual = (t, name, lhs, rhs) =>
  t->test(name, t => {
    t->equal(lhs, rhs, name)

    done()
  })

module Key = {
  type t = int
  let compare = Pervasives.compare
}

module Set = RBTSet.Make(Key)

let empty = Set.empty
let m1 = Set.add(1, empty)

zoraBlock("-- isEmpty --", t => {
  t->testEqual("* empty", empty->Set.isEmpty, true)
  t->testEqual("* not empty", m1->Set.isEmpty, false)
})

zoraBlock("-- add & mem --", t => {
  let m2 = Set.add(2, m1)
  let m3 = Set.add(3, m2)
  t->testEqual("* mem 2", Set.mem(2, m3), true)
})
