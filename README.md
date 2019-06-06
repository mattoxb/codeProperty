# codeProperty

Given a string containing Haskell code, the `isRecursive` function checks to see
if it makes any recursive calls.

They type is `isRecusive :: [String] -> Decl b -> Bool`

The `[String]` argument is the name of any functions we are currently "in".

So far `isRecursive` handles simple function definitions, and can detect recursion inside an auxiliary
definition via `let` or `where`.  Not all expression types are yet supported, and there are some
ways to fool the program that we don't check for yet.

To use, run `stack repl` and use the `check` function.  There are six examples
`ex1` etc.  Or you can parse your own string `code` like:

```
pc = let ParseOk p = parseDecl code in fmap (const ()) p
isRecursive [] pc
```

The `fmap` erases the parse location metadata; otherwise the metadata crowds out the
expression tree.  It is not necessary to call `fmap` to use `isRecursive`.
