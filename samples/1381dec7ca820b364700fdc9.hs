fact :: Integer -> Integer
fact number = helper 1 number
    where helper acc curr | curr == 0 = acc
                          | otherwise = helper (acc*curr) (curr-1)