module type OrderedType = {
  type t
  let compare: (t, t) => int
}

module type S = {
  type key
  type t<'a>
  let empty: t<'a>
  let isEmpty: t<'a> => bool
  let add: (key, 'a, t<'a>) => t<'a>
  let find: (key, t<'a>) => 'a
  let remove: (key, t<'a>) => t<'a>
  let mem: (key, t<'a>) => bool
  let iter: ((key, 'a) => unit, t<'a>) => unit
  let map: ('a => 'b, t<'a>) => t<'b>
  let mapi: ((key, 'a) => 'b, t<'a>) => t<'b>
  let fold: ((key, 'a, 'b) => 'b, t<'a>, 'b) => 'b
  let compare: (('a, 'a) => int, t<'a>, t<'a>) => int
  let equal: (('a, 'a) => bool, t<'a>, t<'a>) => bool
}

module Make = (Ord: OrderedType) => {
  type key = Ord.t

  type rec t<'a> = Black(t<'a>, key, 'a, t<'a>) | Red(t<'a>, key, 'a, t<'a>) | Empty

  type rec enum<'a> = End | More(key, 'a, t<'a>, enum<'a>)

  let rec enum = (m, e) =>
    switch m {
    | Empty => e
    | Black(l, k, x, r) | Red(l, k, x, r) => enum(l, More(k, x, r, e))
    }

  let blackify = n =>
    switch n {
    | Red(l, k, x, r) => (Black(l, k, x, r), false)
    | m => (m, true)
    }

  let empty = Empty

  let isEmpty = m =>
    switch m {
    | Empty => true
    | _ => false
    }

  let balanceLeft = (l, kx, x, r) =>
    switch (l, kx, x, r) {
    | (Red(Red(a, kx, x, b), ky, y, c), kz, z, d)
    | (Red(a, kx, x, Red(b, ky, y, c)), kz, z, d) =>
      Red(Black(a, kx, x, b), ky, y, Black(c, kz, z, d))
    | (l, kx, x, r) => Black(l, kx, x, r)
    }

  let balanceRight = (l, kx, x, r) =>
    switch (l, kx, x, r) {
    | (a, kx, x, Red(Red(b, ky, y, c), kz, z, d))
    | (a, kx, x, Red(b, ky, y, Red(c, kz, z, d))) =>
      Red(Black(a, kx, x, b), ky, y, Black(c, kz, z, d))
    | (l, kx, x, r) => Black(l, kx, x, r)
    }

  let add = (kx, x, m) => {
    let rec add_aux = m =>
      switch m {
      | Empty => Red(Empty, kx, x, Empty)
      | Red(l, ky, y, r) => {
          let c = Ord.compare(kx, ky)
          if c < 0 {
            Red(add_aux(l), ky, y, r)
          } else if c > 0 {
            Red(l, ky, y, add_aux(r))
          } else {
            Red(l, kx, x, r)
          }
        }
      | Black(l, ky, y, r) => {
          let c = Ord.compare(kx, ky)
          if c < 0 {
            balanceLeft(add_aux(l), ky, y, r)
          } else if c > 0 {
            balanceRight(l, ky, y, add_aux(r))
          } else {
            Black(l, kx, x, r)
          }
        }
      }
    fst(blackify(add_aux(m)))
  }

  let rec find = (k, n) =>
    switch n {
    | Empty => raise(Not_found)
    | Red(l, kx, x, r)
    | Black(l, kx, x, r) => {
        let c = Ord.compare(k, kx)
        if c < 0 {
          find(k, l)
        } else if c > 0 {
          find(k, r)
        } else {
          x
        }
      }
    }

  let unbalancedLeft = n =>
    switch n {
    | Red(Black(a, kx, x, b), ky, y, c) => (balanceLeft(Red(a, kx, x, b), ky, y, c), false)
    | Black(Black(a, kx, x, b), ky, y, c) => (balanceLeft(Red(a, kx, x, b), ky, y, c), true)
    | Black(Red(a, kx, x, Black(b, ky, y, c)), kz, z, d) => (
        Black(a, kx, x, balanceLeft(Red(b, ky, y, c), kz, z, d)),
        false,
      )
    | _ => assert false
    }

  let unbalancedRight = n =>
    switch n {
    | Red(a, kx, x, Black(b, ky, y, c)) => (balanceRight(a, kx, x, Red(b, ky, y, c)), false)
    | Black(a, kx, x, Black(b, ky, y, c)) => (balanceRight(a, kx, x, Red(b, ky, y, c)), true)
    | Black(a, kx, x, Red(Black(b, ky, y, c), kz, z, d)) => (
        Black(balanceRight(a, kx, x, Red(b, ky, y, c)), kz, z, d),
        false,
      )
    | _ => assert false
    }

  let rec removeMin = n =>
    switch n {
    | Empty
    | Black(Empty, _, _, Black(_)) =>
      assert false
    | Black(Empty, kx, x, Empty) => (Empty, kx, x, true)
    | Black(Empty, kx, x, Red(l, ky, y, r)) => (Black(l, ky, y, r), kx, x, false)
    | Red(Empty, kx, x, r) => (r, kx, x, false)
    | Black(l, kx, x, r) => {
        let (l, ky, y, d) = removeMin(l)
        let m = Black(l, kx, x, r)
        if d {
          let (m, d) = unbalancedRight(m)
          (m, ky, y, d)
        } else {
          (m, ky, y, false)
        }
      }
    | Red(l, kx, x, r) => {
        let (l, ky, y, d) = removeMin(l)
        let m = Red(l, kx, x, r)
        if d {
          let (m, d) = unbalancedRight(m)
          (m, ky, y, d)
        } else {
          (m, ky, y, false)
        }
      }
    }

  let remove = (k, m) => {
    let rec removeAux = n =>
      switch n {
      | Empty => (Empty, false)
      | Black(l, kx, x, r) => {
          let c = Ord.compare(k, kx)
          if c < 0 {
            let (l, d) = removeAux(l)
            let m = Black(l, kx, x, r)
            if d {
              unbalancedRight(m)
            } else {
              (m, false)
            }
          } else if c < 0 {
            let (r, d) = removeAux(r)
            let m = Black(l, kx, x, r)
            if d {
              unbalancedLeft(m)
            } else {
              (m, false)
            }
          } else {
            switch r {
            | Empty => blackify(l)
            | _ => {
                let (r, kx, x, d) = removeMin(r)
                let m = Black(l, kx, x, r)
                if d {
                  unbalancedLeft(m)
                } else {
                  (m, false)
                }
              }
            }
          }
        }
      | Red(l, kx, x, r) => {
          let c = Ord.compare(k, kx)
          if c < 0 {
            let (l, d) = removeAux(l)
            let m = Red(l, kx, x, r)
            if d {
              unbalancedRight(m)
            } else {
              (m, false)
            }
          } else if c > 0 {
            let (r, d) = removeAux(r)
            let m = Red(l, kx, x, r)
            if d {
              unbalancedLeft(m)
            } else {
              (m, false)
            }
          } else {
            switch r {
            | Empty => (l, false)
            | _ => {
                let (r, kx, x, d) = removeMin(r)
                let m = Red(l, kx, x, r)
                if d {
                  unbalancedLeft(m)
                } else {
                  (m, false)
                }
              }
            }
          }
        }
      }
    fst(removeAux(m))
  }

  let rec mem = (k, n) =>
    switch n {
    | Empty => false
    | Red(l, kx, _x, r)
    | Black(l, kx, _x, r) => {
        let c = Ord.compare(k, kx)
        if c < 0 {
          mem(k, l)
        } else if c > 0 {
          mem(k, r)
        } else {
          true
        }
      }
    }

  let rec iter = (f, n) =>
    switch n {
    | Empty => ()
    | Red(l, k, x, r) | Black(l, k, x, r) => {
        iter(f, l)
        f(k, x)
        iter(f, r)
      }
    }

  let rec map = (f, n) =>
    switch n {
    | Empty => Empty
    | Red(l, k, x, r) => Red(map(f, l), k, f(x), map(f, r))
    | Black(l, k, x, r) => Black(map(f, l), k, f(x), map(f, r))
    }

  let rec mapi = (f, n) =>
    switch n {
    | Empty => Empty
    | Red(l, k, x, r) => Red(mapi(f, l), k, f(k, x), mapi(f, r))
    | Black(l, k, x, r) => Black(mapi(f, l), k, f(k, x), mapi(f, r))
    }

  let rec fold = (f, m, accu) =>
    switch m {
    | Empty => accu
    | Red(l, k, x, r) | Black(l, k, x, r) => fold(f, r, f(k, x, fold(f, l, accu)))
    }

  let compare = (cmp, m1, m2) => {
    let rec compareAux = (e1, e2) =>
      switch (e1, e2) {
      | (End, End) => 0
      | (End, _) => -1
      | (_, End) => 1
      | (More(k1, x1, r1, e1), More(k2, x2, r2, e2)) => {
          let c = Ord.compare(k1, k2)
          if c != 0 {
            c
          } else {
            let c = cmp(x1, x2)
            if c != 0 {
              c
            } else {
              compareAux(enum(r1, e1), enum(r2, e2))
            }
          }
        }
      }
    compareAux(enum(m1, End), enum(m2, End))
  }

  let equal = (cmp, m1, m2) => {
    let rec equalAux = (e1, e2) =>
      switch (e1, e2) {
      | (End, End) => true
      | (End, _)
      | (_, End) => false
      | (More(k1, x1, r1, e1), More(k2, x2, r2, e2)) =>
        Ord.compare(k1, k2) == 0 && cmp(x1, x2) && equalAux(enum(r1, e1), enum(r2, e2))
      }
    equalAux(enum(m1, End), enum(m2, End))
  }
}
