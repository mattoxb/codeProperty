
fact :: Integer -> Integer
fact n = aux n 1
  where
    aux 0 c = c
    aux n c = aux (n -1) (c * n)