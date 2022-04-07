@ocaml.doc("Input signature of the functor {!Rbset.Make}.")
module type OrderedType = {
  @ocaml.doc("The type of the set elements.")
  type t

  @ocaml.doc("
  A total ordering function over the set elements.
  This is a two-argument function [f] such that
  [f e1 e2] is zero if the elements [e1] and [e2] are equal,
  [f e1 e2] is strictly negative if [e1] is smaller than [e2],
  and [f e1 e2] is strictly positive if [e1] is greater than [e2].
  Example: a suitable ordering function is the generic structural
  comparison function {!Pervasives.compare}.
  ")
  let compare: (t, t) => int
}

module type S = {
  @ocaml.doc("The type of the set elements.")
  type elt

  @ocaml.doc("The type of sets.")
  type t

  @ocaml.doc("The empty set.")
  let empty: t

  @ocaml.doc("Test whether a set is empty or not.")
  let isEmpty: t => bool

  @ocaml.doc("[mem x s] tests whether [x] belongs to the set [s].")
  let mem: (t, elt) => bool

  @ocaml.doc("
  [add x s] returns a set containing all elements of [s],
  plus [x]. If [x] was already in [s], [s] is returned unchanged.
  ")
  let add: (t, elt) => t

  @ocaml.doc("[singleton x] returns the one-element set containing only [x].")
  let singleton: elt => t

  @ocaml.doc("
  [remove x s] returns a set containing all elements of [s],
  except [x]. If [x] was not in [s], [s] is returned unchanged.
  ")
  let remove: (t, elt) => t

  @ocaml.doc("Set union.")
  let union: (t, t) => t

  @ocaml.doc("Set intersection.")
  let inter: (t, t) => t

  @ocaml.doc("Set difference.")
  let diff: (t, t) => t

  @ocaml.doc("
  Total ordering between sets. Can be used as the ordering function
  for doing sets of sets.
  ")
  let compare: (t, t) => int

  @ocaml.doc("
  [equal s1 s2] tests whether the sets [s1] and [s2] are
  equal, that is, contain equal elements.
  ")
  let equal: (t, t) => bool

  @ocaml.doc("
  [subset s1 s2] tests whether the set [s1] is a subset of
  the set [s2].
  ")
  let subset: (t, t) => bool

  @ocaml.doc("
  [iter f s] applies [f] in turn to all elements of [s].
  The elements of [s] are presented to [f] in increasing order
  with respect to the ordering over the type of the elements.
  ")
  let iter: (t, elt => unit) => unit

  @ocaml.doc("
  [fold f s a] computes [(f xN ... (f x2 (f x1 a))...)],
  where [x1 ... xN] are the elements of [s], in increasing order.
  ")
  let fold: (t, (elt, 'a) => 'a, 'a) => 'a

  @ocaml.doc("
  [for_all p s] checks if all elements of the set
  satisfy the predicate [p].
  ")
  let forAll: (t, elt => bool) => bool

  @ocaml.doc("
  [exists p s] checks if at least one element of
  the set satisfies the predicate [p].
  ")
  let exists: (t, elt => bool) => bool

  @ocaml.doc("
  [filter p s] returns the set of all elements in [s]
  that satisfy predicate [p].
  ")
  let filter: (t, elt => bool) => t

  @ocaml.doc("
  [partition p s] returns a pair of sets [(s1, s2)], where
  [s1] is the set of all the elements of [s] that satisfy the
  predicate [p], and [s2] is the set of all the elements of
  [s] that do not satisfy [p].
  ")
  let partition: (t, elt => bool) => (t, t)

  @ocaml.doc("Return the number of elements of a set.")
  let cardinal: t => int

  @ocaml.doc("
  Return the list of all elements of the given set.
  The returned list is sorted in increasing order with respect
  to the ordering [Ord.compare], where [Ord] is the argument
  given to {!Set.Make}.
  ")
  let elements: t => list<elt>

  @ocaml.doc("
  Return the smallest element of the given set
  (with respect to the [Ord.compare] ordering), or raise
  [Not_found] if the set is empty.
  ")
  let minElt: t => elt

  @ocaml.doc("
  Same as {!Set.S.min_elt}, but returns the largest element of the
  given set.
  ")
  let maxElt: t => elt

  @ocaml.doc("
  Return one element of the given set, or raise [Not_found] if
  the set is empty. Which element is chosen is unspecified,
  but equal elements will be chosen for equal sets.
  ")
  let choose: t => elt

  @ocaml.doc("
  [split x s] returns a triple [(l, present, r)], where
  [l] is the set of elements of [s] that are
  strictly less than [x];
  [r] is the set of elements of [s] that are
  strictly greater than [x];
  [present] is [false] if [s] contains no element equal to [x],
  or [true] if [s] contains an element equal to [x].
  ")
  let split: (t, elt) => (t, bool, t)
}

@ocaml.doc("
Functor building an implementation of the set structure
given a totally ordered type.
")
module Make: (Ord: OrderedType) => (S with type elt = Ord.t)
