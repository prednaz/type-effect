let f = fn a => a + 1 in
let g = fn a => a + 1 in
let h = if false then f else g in
f
