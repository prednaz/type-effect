let f = fn h => h 0 + 0 in
let g = fn h => h 0 + 0 in
let h = fn a => a in
let x = f h in
let y = g h in
if false then f else g