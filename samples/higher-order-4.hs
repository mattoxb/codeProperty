factk :: Integer -> (a -> Integer)
factk n = aux 1 n where
  aux acc 0 = \_ -> acc
  aux acc n = aux (acc*n) (n-1)
