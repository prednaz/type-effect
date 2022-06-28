let const = fn a => (fn b => a) in
let f = fn h => const (fn a => a) (h 0) in
let g = fn h => const (fn a => a) (h 0) in
let x = f (fn a => a) in
let y = g (fn a => a) in
if false then f else g