fact :: Integer -> Integer
aux :: Integer -> Integer -> Integer
fact n = aux n 1

aux n a
    | (n == 1) = a
    | otherwise = (aux (n-1) (n*a))