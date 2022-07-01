let unify = fn a => fn b => if false then a else b in
let f = fn a => a in
let g = fn a => a in
let z = unify f g in
f
