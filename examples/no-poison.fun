let f = fn x => x + 1 in
let g = fn y => y * 3 in
let h = fn z => (if false then f else g) in
f 