let append =
     fun f xs =>
    (fn ys => lcase xs of Cons(hd, tl) =>
        Cons(hd, f tl ys)
     or ys
    ) in
append