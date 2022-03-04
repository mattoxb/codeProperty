fact :: Integer -> Integer
fact 0 = 1
fact n = let m = fact (n - 1) in n * m
