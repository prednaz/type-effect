let f = fn g => g 0 in
let z = f (fn x => x) + 1 in
f