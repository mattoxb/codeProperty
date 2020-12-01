fact :: Integer -> Integer
fact 0 = 1
fact a = a*fact (a-1)