fact :: Integer -> Integer
fact x = func x 1
    where
        func 0 y = y
        func x y = func (x - 1) (x * y)