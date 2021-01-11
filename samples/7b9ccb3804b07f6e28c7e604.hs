fact :: Integer -> Integer
fact n = aux n 1 where
    aux :: Integer -> Integer -> Integer
    aux 0 acc = acc
    aux n acc = aux (n - 1) (acc * n)