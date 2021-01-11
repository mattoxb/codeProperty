fact :: Integer -> Integer
fact xx = aux xx 0
    where
        aux 1 res = res
        aux x res = aux x-1 x*res