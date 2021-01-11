fact :: Integer -> Integer
fact x = check x 1
    where check _ x = x 
check x a = x * (check (x-1) a)