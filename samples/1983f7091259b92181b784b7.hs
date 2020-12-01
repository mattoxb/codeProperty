fact :: Integer -> Integer
fact n = aux n 1
    where   aux 0 a = a
            aux n a = aux (n-1) (n*a)