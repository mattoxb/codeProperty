fact :: Integer -> Integer
aux 1 accum = accum
aux n accum = aux (n-1) (accum*n)
fact n = aux n 1 