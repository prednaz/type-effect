(fn f =>
  let g = fn a => a in
  let z = if false then f else g in
  f
)
  (fn a => a)
