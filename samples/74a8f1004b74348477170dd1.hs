fact :: Integer -> Integer
fact 0 = 0
fact 1 = 1
fact x = x * fact(x-1)