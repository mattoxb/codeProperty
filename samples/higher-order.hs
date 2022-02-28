factk :: Integer -> (Integer -> t) -> t
factk n k = aux 1 n where
  aux acc 0 = k acc
  aux acc n = aux (n*acc) (n-1)
