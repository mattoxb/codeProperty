fact :: Integer -> Integer
fact n = aux 1 1
    where aux c k
            | c == n = (k*c)
            | otherwise = aux (c+1) (k*c)