let unify = fn a => (fn b => if false then a else b) in
let f = fn a => unify (fn a => a) (fn a => fn a) in
let g = fn a => unify (fn a => a) (fn a => fn a) in
unify f g 