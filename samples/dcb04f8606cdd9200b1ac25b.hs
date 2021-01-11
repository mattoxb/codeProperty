fact :: Integer -> Integer
aux :: Integer -> Integer -> Integer
fact n = (aux n 1)

aux 1 _ = 1
aux n a = (aux (n-1) a*n)