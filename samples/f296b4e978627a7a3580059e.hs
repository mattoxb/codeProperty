fact :: Integer -> Integer
fact 1 = 1
fact a = aux a 1
    where
        aux 0 n = n
        aux a n = aux (a-1) (a*n)