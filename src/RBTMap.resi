@ocaml.doc("Input signature of the functor {!Map.Make}.")
module type OrderedType = {
  @ocaml.doc("The type of the map keys.")
  type t
  @ocaml.doc("
  A total ordering function over the keys.
  This is a two-argument function [f] such that
  [f e1 e2] is zero if the keys [e1] and [e2] are equal,
  [f e1 e2] is strictly negative if [e1] is smaller than [e2],
  and [f e1 e2] is strictly positive if [e1] is greater than [e2].
  Example: a suitable ordering function is the generic structural
  comparison function {!Pervasives.compare}.
  ")
  let compare: (t, t) => int
}

module type S = {
  @ocaml.doc("The type of the map keys.")
  type key

  @ocaml.doc("The type of maps from type [key] to type ['a].")
  type t<'a>

  @ocaml.doc("The empty map.")
  let empty: t<'a>

  @ocaml.doc("Test whether a map is empty or not.")
  let isEmpty: t<'a> => bool

  @ocaml.doc("
  [add x y m] returns a map containing the same bindings as
  [m], plus a binding of [x] to [y]. If [x] was already bound
  in [m], its previous binding disappears.
  ")
  let add: (t<'a>, key, 'a) => t<'a>

  @ocaml.doc("
  [find x m] returns the current binding of [x] in [m],
  or raises [Not_found] if no such binding exists.
  ")
  let find: (t<'a>, key) => 'a

  @ocaml.doc("
  [remove x m] returns a map containing the same bindings as
  [m], except for [x] which is unbound in the returned map.
  ")
  let remove: (t<'a>, key) => t<'a>

  @ocaml.doc("
  [mem x m] returns [true] if [m] contains a binding for [x],
  and [false] otherwise.
  ")
  let mem: (t<'a>, key) => bool

  @ocaml.doc("
  [iter f m] applies [f] to all bindings in map [m].
  [f] receives the key as first argument, and the associated value
  as second argument.  The bindings are passed to [f] in increasing
  order with respect to the ordering over the type of the keys.
  ")
  let iter: (t<'a>, (key, 'a) => unit) => unit

  @ocaml.doc("
  [map f m] returns a map with same domain as [m], where the
  associated value [a] of all bindings of [m] has been
  replaced by the result of the application of [f] to [a].
  The bindings are passed to [f] in increasing order
  with respect to the ordering over the type of the keys.
  ")
  let map: (t<'a>, 'a => 'b) => t<'b>

  @ocaml.doc("
  Same as {!Map.S.map}, but the function receives as arguments both the
  key and the associated value for each binding of the map.
  ")
  let mapi: (t<'a>, (key, 'a) => 'b) => t<'b>

  @ocaml.doc("
  [fold f m a] computes [(f kN dN ... (f k1 d1 a)...)],
  where [k1 ... kN] are the keys of all bindings in [m]
  (in increasing order), and [d1 ... dN] are the associated data.
  ")
  let fold: (t<'a>, (key, 'a, 'b) => 'b, 'b) => 'b

  @ocaml.doc("
  Total ordering between maps.  The first argument is a total ordering
  used to compare data associated with equal keys in the two maps.
  ")
  let compare: (t<'a>, t<'a>, ('a, 'a) => int) => int

  @ocaml.doc("
  [equal cmp m1 m2] tests whether the maps [m1] and [m2] are
  equal, that is, contain equal keys and associate them with
  equal data.  [cmp] is the equality predicate used to compare
  the data associated with the keys.
  ")
  let equal: (t<'a>, t<'a>, ('a, 'a) => bool) => bool
}

@ocaml.doc("
Functor building an implementation of the map structure
given a totally ordered type.
")
module Make: (Ord: OrderedType) => (S with type key = Ord.t)
