fact :: Integer -> Integer
fact n = (ax n 1)
        where
        (ax 1 t) = 1
        (ax n t) = n*(ax n-1 t)