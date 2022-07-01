let f = fn a => a (fn a => a) in
let g = fn a => a (fn a => a) in
let z = if false then f else g in
f
