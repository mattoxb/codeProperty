fact :: Integer -> Integer
fact a
    | a <= 0        = 1
    | otherwise     = a * fact (a - 1)