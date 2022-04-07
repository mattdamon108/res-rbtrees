module type OrderedType = {
  type t
  let compare: (t, t) => int
}

module type S = {
  type elt
  type t
  let empty: t
  let isEmpty: t => bool
  let mem: (elt, t) => bool
  let add: (elt, t) => t
  let singleton: elt => t
  let remove: (elt, t) => t
  let union: (t, t) => t
  let inter: (t, t) => t
  let diff: (t, t) => t
  let compare: (t, t) => int
  let equal: (t, t) => bool
  let subset: (t, t) => bool
  let iter: (elt => unit, t) => unit
  let fold: ((elt, 'a) => 'a, t, 'a) => 'a
  let forAll: (elt => bool, t) => bool
  let exists: (elt => bool, t) => bool
  let filter: (elt => bool, t) => t
  let partition: (elt => bool, t) => (t, t)
  let cardinal: t => int
  let elements: t => list<elt>
  let minElt: t => elt
  let maxElt: t => elt
  let choose: t => elt
  let split: (elt, t) => (t, bool, t)
}

module Make = (Ord: OrderedType) => {
  type elt = Ord.t

  type rec t = Black(t, elt, t) | Red(t, elt, t) | Empty

  type rec enum = End | More(elt, t, enum)

  let rec enum = (s, e) =>
    switch s {
    | Empty => e
    | Black(l, x, r) | Red(l, x, r) => enum(l, More(x, r, e))
    }

  let blackify = n =>
    switch n {
    | Red(l, x, r) => (Black(l, x, r), false)
    | s => (s, true)
    }

  let empty = Empty

  let isEmpty = s =>
    switch s {
    | Empty => true
    | _ => false
    }

  let balanceLeft = (l, x, r) =>
    switch (l, x, r) {
    | (Red(Red(a, x, b), y, c), z, d)
    | (Red(a, x, Red(b, y, c)), z, d) =>
      Red(Black(a, x, b), y, Black(c, z, d))
    | (l, x, r) => Black(l, x, r)
    }

  let balanceRight = (l, x, r) =>
    switch (l, x, r) {
    | (a, x, Red(Red(b, y, c), z, d))
    | (a, x, Red(b, y, Red(c, z, d))) =>
      Red(Black(a, x, b), y, Black(c, z, d))
    | (l, x, r) => Black(l, x, r)
    }

  let add = (x, s) => {
    let rec addAux = s =>
      switch s {
      | Empty => Red(Empty, x, Empty)
      | Red(l, y, r) as s => {
          let c = Ord.compare(x, y)
          if c < 0 {
            Red(addAux(l), y, r)
          } else if c > 0 {
            Red(l, y, addAux(r))
          } else {
            s
          }
        }
      | Black(l, y, r) as s => {
          let c = Ord.compare(x, y)
          if c < 0 {
            balanceLeft(addAux(l), y, r)
          } else if c > 0 {
            balanceRight(l, y, addAux(r))
          } else {
            s
          }
        }
      }
    fst(blackify(addAux(s)))
  }

  let rec mem = (x, s) =>
    switch s {
    | Empty => false
    | Red(l, y, r)
    | Black(l, y, r) => {
        let c = Ord.compare(x, y)
        if c < 0 {
          mem(x, l)
        } else if c > 0 {
          mem(x, r)
        } else {
          true
        }
      }
    }

  let singleton = x => Black(Empty, x, Empty)

  let unbalancedLeft = s =>
    switch s {
    | Red(Black(a, x, b), y, c) => (balanceLeft(Red(a, x, b), y, c), false)
    | Black(Black(a, x, b), y, c) => (balanceLeft(Red(a, x, b), y, c), true)
    | Black(Red(a, x, Black(b, y, c)), z, d) => (
        Black(a, x, balanceLeft(Red(b, y, c), z, d)),
        false,
      )
    | _ => assert false
    }

  let unbalancedRight = s =>
    switch s {
    | Red(a, x, Black(b, y, c)) => (balanceRight(a, x, Red(b, y, c)), false)
    | Black(a, x, Black(b, y, c)) => (balanceRight(a, x, Red(b, y, c)), true)
    | Black(a, x, Red(Black(b, y, c), z, d)) => (
        Black(balanceRight(a, x, Red(b, y, c)), z, d),
        false,
      )
    | _ => assert false
    }

  let rec removeMin = s =>
    switch s {
    | Empty
    | Black(Empty, _, Black(_)) =>
      assert false
    | Black(Empty, x, Empty) => (Empty, x, true)
    | Black(Empty, x, Red(l, y, r)) => (Black(l, y, r), x, false)
    | Red(Empty, x, r) => (r, x, false)
    | Black(l, x, r) => {
        let (l, y, d) = removeMin(l)
        let s = Black(l, x, r)
        if d {
          let (s, d) = unbalancedRight(s)
          (s, y, d)
        } else {
          (s, y, false)
        }
      }
    | Red(l, x, r) => {
        let (l, y, d) = removeMin(l)
        let s = Red(l, x, r)
        if d {
          let (s, d) = unbalancedRight(s)
          (s, y, d)
        } else {
          (s, y, false)
        }
      }
    }

  let remove = (x, s) => {
    let rec removeAux = s =>
      switch s {
      | Empty => (Empty, false)
      | Black(l, y, r) => {
          let c = Ord.compare(x, y)
          if c < 0 {
            let (l, d) = removeAux(l)
            let s = Black(l, y, r)
            if d {
              unbalancedRight(s)
            } else {
              (s, false)
            }
          } else if c > 0 {
            let (r, d) = removeAux(r)
            let s = Black(l, y, r)
            if d {
              unbalancedLeft(s)
            } else {
              (s, false)
            }
          } else {
            switch r {
            | Empty => blackify(l)
            | _ => {
                let (r, y, d) = removeMin(r)
                let s = Black(l, y, r)
                if d {
                  unbalancedLeft(s)
                } else {
                  (s, false)
                }
              }
            }
          }
        }
      | Red(l, y, r) => {
          let c = Ord.compare(x, y)
          if c < 0 {
            let (l, d) = removeAux(l)
            let s = Red(l, y, r)
            if d {
              unbalancedRight(s)
            } else {
              (s, false)
            }
          } else if c > 0 {
            let (r, d) = removeAux(r)
            let s = Red(l, y, r)
            if d {
              unbalancedLeft(s)
            } else {
              (s, false)
            }
          } else {
            switch r {
            | Empty => (l, false)
            | _ => {
                let (r, y, d) = removeMin(r)
                let s = Red(l, y, r)
                if d {
                  unbalancedLeft(s)
                } else {
                  (s, false)
                }
              }
            }
          }
        }
      }
    fst(removeAux(s))
  }

  let union = (s1, s2) => {
    let rec unionAux = (e1, e2, accu) =>
      switch (e1, e2) {
      | (End, End) => accu
      | (End, More(x, r, e))
      | (More(x, r, e), End) =>
        unionAux(End, enum(r, e), add(x, accu))
      | (More(x1, r1, e1) as e1', More(x2, r2, e2) as e2') => {
          let c = Ord.compare(x1, x2)
          if c < 0 {
            unionAux(enum(r1, e1), e2', add(x1, accu))
          } else if c > 0 {
            unionAux(e1', enum(r2, e2), add(x2, accu))
          } else {
            unionAux(enum(r1, e1), enum(r2, e2), add(x1, accu))
          }
        }
      }
    unionAux(enum(s1, End), enum(s2, End), Empty)
  }

  let inter = (s1, s2) => {
    let rec interAux = (e1, e2, accu) =>
      switch (e1, e2) {
      | (End, _)
      | (_, End) => accu
      | (More(x1, r1, e1) as e1', More(x2, r2, e2) as e2') => {
          let c = Ord.compare(x1, x2)
          if c < 0 {
            interAux(enum(r1, e1), e2', accu)
          } else if c > 0 {
            interAux(e1', enum(r2, e2), accu)
          } else {
            interAux(enum(r1, e1), enum(r2, e2), add(x1, accu))
          }
        }
      }
    interAux(enum(s1, End), enum(s2, End), Empty)
  }

  let diff = (s1, s2) => {
    let rec diffAux = (e1, e2, accu) =>
      switch (e1, e2) {
      | (End, _) => accu
      | (More(x, r, e), End) => diffAux(enum(r, e), End, add(x, accu))
      | (More(x1, r1, e1) as e1', More(x2, r2, e2) as e2') => {
          let c = Ord.compare(x1, x2)
          if c < 0 {
            diffAux(enum(r1, e1), e2', add(x1, accu))
          } else if c > 0 {
            diffAux(e1', enum(r2, e2), accu)
          } else {
            diffAux(enum(r1, e1), enum(r2, e2), accu)
          }
        }
      }
    diffAux(enum(s1, End), enum(s2, End), Empty)
  }

  let compare = (s1, s2) => {
    let rec compareAux = (e1, e2) =>
      switch (e1, e2) {
      | (End, End) => 0
      | (End, _) => -1
      | (_, End) => 1
      | (More(x1, r1, e1), More(x2, r2, e2)) => {
          let c = Ord.compare(x1, x2)
          if c != 0 {
            c
          } else {
            compareAux(enum(r1, e1), enum(r2, e2))
          }
        }
      }
    compareAux(enum(s1, End), enum(s2, End))
  }

  let equal = (s1, s2) => compare(s1, s2) == 0

  let rec subset = (s1, s2) =>
    switch (s1, s2) {
    | (Empty, _) => true
    | (_, Empty) => false
    | (Black(l1, x1, r1) | Red(l1, x1, r1), (Black(l2, x2, r2) | Red(l2, x2, r2)) as s2) => {
        let c = Ord.compare(x1, x2)
        if c == 0 {
          subset(l1, l2) && subset(r1, r2)
        } else if c < 0 {
          subset(Black(l1, x1, Empty), l2) && subset(r1, s2)
        } else {
          subset(Black(Empty, x1, r1), r2) && subset(l1, s2)
        }
      }
    }

  let rec iter = (f, s) =>
    switch s {
    | Empty => ()
    | Black(l, x, r) | Red(l, x, r) => {
        iter(f, l)
        f(x)
        iter(f, r)
      }
    }

  let rec fold = (f, s, accu) =>
    switch s {
    | Empty => accu
    | Black(l, x, r) | Red(l, x, r) => fold(f, r, f(x, fold(f, l, accu)))
    }

  let rec forAll = (p, s) =>
    switch s {
    | Empty => true
    | Black(l, x, r) | Red(l, x, r) => p(x) && (forAll(p, l) && forAll(p, r))
    }

  let rec exists = (p, s) =>
    switch s {
    | Empty => false
    | Black(l, x, r) | Red(l, x, r) => p(x) || (exists(p, l) || exists(p, r))
    }

  let filter = (p, s) => {
    let rec filterAux = (accu, s) =>
      switch s {
      | Empty => accu
      | Black(l, x, r) | Red(l, x, r) =>
        filterAux(
          filterAux(
            if p(x) {
              add(x, accu)
            } else {
              accu
            },
            l,
          ),
          r,
        )
      }
    filterAux(Empty, s)
  }

  let partition = (p, s) => {
    let rec partitionAux = ((t, f) as accu, s) =>
      switch s {
      | Empty => accu
      | Black(l, x, r) | Red(l, x, r) =>
        partitionAux(
          partitionAux(
            if p(x) {
              (add(x, t), f)
            } else {
              (t, add(x, f))
            },
            l,
          ),
          r,
        )
      }
    partitionAux((Empty, Empty), s)
  }

  let rec cardinal = s =>
    switch s {
    | Empty => 0
    | Black(l, _x, r) | Red(l, _x, r) => 1 + cardinal(l) + cardinal(r)
    }

  let rec elementsAux = (accu, s) =>
    switch s {
    | Empty => accu
    | Black(l, x, r) | Red(l, x, r) => elementsAux(list{x, ...elementsAux(accu, r)}, l)
    }

  let elements = s => elementsAux(list{}, s)

  let rec minElt = s =>
    switch s {
    | Empty => raise(Not_found)
    | Black(Empty, x, _) | Red(Empty, x, _) => x
    | Black(l, _, _) | Red(l, _, _) => minElt(l)
    }

  let rec maxElt = s =>
    switch s {
    | Empty => raise(Not_found)
    | Black(_, x, Empty) | Red(_, x, Empty) => x
    | Black(_, _, r) | Red(_, _, r) => maxElt(r)
    }

  let choose = s =>
    switch s {
    | Empty => raise(Not_found)
    | Black(_, x, _) | Red(_, x, _) => x
    }

  let split = (x, s) => {
    let splitAux = (y, (l, b, r)) => {
      let c = Ord.compare(x, y)
      if c < 0 {
        (l, b, add(x, r))
      } else if c > 0 {
        (add(x, l), b, r)
      } else {
        (l, true, r)
      }
    }
    fold(splitAux, s, (Empty, false, Empty))
  }
}
