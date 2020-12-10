# codeProperty

## As An Executable
The `codeProperty` executable checks that certain functions in a single file
are tail-recursive. The syntax is

```bash
$ codeProperty filepath name1 name2...
```

Where the `name`s are the names of the functions to check. 

`codeProperty` won't
allow _any_ functions in the module to be directly recursive, but will allow
other functions to be tail-recursive or non-recursive. Therefore, it's
recommended that you make sure the standard `Prelude` higher order functions
such as `map` and `filter` are not imported in the module being checked.
`codeProperty` won't check for that itself. However `codeProperty` will
identify and reject list comprehensions.

There are still a few ways to fool `codeProperty` but they would essentially
require being able to write a properly tail-recursive function anyways.
`codeProperty` won't notice mutual recursion (tail or otherwise) and
additionally it won't detect recursion introduced by `Data.Function.fix` or
any similar fixpoint operator. In order to use these methods to fool 
`codeProperty`, one would have to write a function that _looked_ tail
recursive but actually used a workaround to do the work. This is pretty hard
for someone who couldn't write a working tail-recursive definition and so
we feel this backdoor is acceptable.

A future release may fix the mutual recursion detection, but it is not possible
in general (see Rice's Theorem) to detect fixpoint combinators.

## As A Library
`codeProperty` currently isn't intended to be used as a library, but one could
build it from source and use it like one. One potentially useful function
exported from the `Lib` module is

```haskell
testModuleFromFile :: FilePath -> [Name] -> IO Bool
```

which is essentially the same as the `codeProperty` executable itself. However,
be aware that errors will still be raised (synchronously) instead of returning
`False`. Any of the usual Haskell unit testing libraries should be equipped to
handle this behavior.
