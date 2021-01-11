fact :: Integer -> Integer
fact n = go n 1
    where
        go 0 x = x
        go n x = go (n-1) (n*x)