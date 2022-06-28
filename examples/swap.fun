let swap = fn p => (pcase p of (x , y) => pair (y , x)) in
let f = fn x => x in
let g = fn y => y in 
let p = swap (pair (f , g)) in
pcase p of (h , k)