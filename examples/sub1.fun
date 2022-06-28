let f = fn h => h 0 + 0 in
let g = fn h => h 0 + 0 in
let x = f (fn a => a) in
if false then f else g