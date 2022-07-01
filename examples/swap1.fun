let swap = fn p => (pcase p of Pair (x , y) => Pair (y , x)) in
let f = fn x => x in
let g = fn y => y in 
let p = swap (Pair (f , g)) in
pcase p of Pair (h , k) => k
