fact :: Integer -> Integer
aux :: Integer -> Integer -> Integer
aux n cur
    | (n == 1) = cur
    | otherwise = n*(aux (n-1) cur)
fact n = aux n 1
 