let f = fn a => a + 1 in
let g = fn a => a + 1 in
let h = (fn b => fn c => if false then b else c) f g in
f
