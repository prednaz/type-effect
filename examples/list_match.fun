lcase Cons(fn a => a, Cons(fn a => a, Nil)) of
  Cons(a, b) => b
  or Nil
