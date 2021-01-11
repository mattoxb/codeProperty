fact :: Integer -> Integer
fact xx = aux xx 1
    where 
        aux 0 a = a
        aux x a = aux (x-1) (a*x)