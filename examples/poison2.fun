let f = fn a => a 0 + 0 in
let g = fn a => a 0 + 0 in
let x = f (fn a => a + 0) in
let y = g (fn a => a + 0) in
let z = if false then f else g in
g