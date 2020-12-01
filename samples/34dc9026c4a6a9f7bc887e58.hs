fact :: Integer -> Integer
fact x = aux x 1
        where
        aux 0 t = t
        aux x t = x * (aux (x - 1) t)