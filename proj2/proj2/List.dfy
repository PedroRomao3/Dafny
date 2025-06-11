/*===============================================
  M.EIC037: Formal Methods For Critical Systems

  Project 2 support file

  ===============================================*/

module List {
  datatype List<T> = Nil | Cons(head: T, tail: List<T>) 

  ghost function elements<T>(l: List<T>): set<T>
    ensures l != Nil ==> elements(l.tail) <= elements(l)
  { 
    match l
    case Nil => {}
    case Cons(h, t) => {h} + elements(t)
  }

  ghost function elementSeq<T>(l: List<T>): seq<T>
    ensures len(l) == |elementSeq(l)|
  {
    match l
    case Nil => []
    case Cons(h, t) => [h] + elementSeq(t)
  }

  ghost function elementBag<T>(l: List<T>): multiset<T>
  { 
    match l
    case Nil => multiset{}
    case Cons(h, t) => multiset{h} + elementBag(t)
  }

  function len<T>(l: List<T>): int
    ensures len(l) >= |elements(l)|
  {
    match l
    case Nil => 0
    case Cons(_, t) => 1 + len(t)
  }

  function count<T(==)>(l: List<T>, x: T): nat
  {
    match l
    case Nil => 0
    case Cons(h, t) => (if h == x then 1 else 0) + count(t, x)
  }

  function at<T>(l: List<T>, i: nat): T
    requires i < len(l)
  {
    if i == 0 then l.head else at(l.tail, i - 1)
  }

  function append<T>(l1: List<T>, l2: List<T>): List<T>
    ensures len(append(l1, l2)) == len(l1) + len(l2)
  {
    match l1
    case Nil => l2
    case Cons(h, t) => Cons(h, append(t, l2))
  }

  function take<T>(l: List<T>, n: nat): List<T>
    requires n <= len(l) 
    ensures len(take(l, n)) == n
  {
    if n == 0 then Nil else Cons(l.head, take(l.tail, n - 1))
  }

  function drop<T>(l: List<T>, n: nat): List<T>
    requires n <= len(l) 
    ensures len(drop(l, n)) == len(l) - n
  {
    if n == 0 then l else drop(l.tail, n - 1)
  }

  function remove<T(==)>(l: List<T>, x: T): List<T>
    decreases l
    ensures var l' := remove(l, x);
            x !in elements(l')
            && elements(l') == elements(l) - {x}
  { 
    match l 
    case Nil => Nil
    case Cons(h, t) => 
      if x == h then remove(t, x)
      else Cons(h, remove(t, x))
  }
}
