let f = fn x => x + 1 in
let g = fn y => y * 2 in
let h = fn z => z 3 in
let k = h g + h f in
h