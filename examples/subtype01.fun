let f = fn a => a 0 in
let x = f (fn a => a) in
let g = fn a => a 0 in
let y = g (fn a => a) in
let z = if false then f else g in
z