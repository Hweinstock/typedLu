# project-cis5520

This is an "Empty project" for Haskell. It is configured in the same way as
the lecture demo and homework assignments for CIS 5520, but contains no
code. Feel free to use this repository for experimentation!

If you want to change the name of this project, look for all occurrences of
`project-cis5520` in the `project-cis5520.cabal` file and in the `hie.yaml` 
file. (And change the name of the cabal file to match your new name!)

## Module organization

Haskell packages typically divide their source code into three separate places:

  - The bulk of your code should be developed as a reusable library in 
    modules in the `src` directory. We've created [Lib.hs](src/Lib.hs) 
    for you to get started. You can add additional modules here.
  
  - The entry point for your executable is in [Main.hs](app/Main.hs). 
  
  - All of your test cases should be in [the test directory](test/Spec.hs).

## Building, running, and testing

This project compiles with `stack build`. 
You can run the main executable with `stack run`.
You can run the tests with `stack test`. 

Finally, you can start a REPL with `stack ghci`.

## Importing additional libraries

This project is designed to run with stackage: you can easily use any library
in https://www.stackage.org/lts-21.6 by adding an entry to the
`build-depends` list of the `common-stanza` in the cabal file. If you want to
use a library that is not on stackage, you'll need to update the common-stanza
*and* add information to `stack.yaml` about where to find that library.

## TODO 
CP1:
- [x] Define type `datatype`.
- [x] Create bare-bones `LuTypeChecker` module.
- [x] Outline arbitrary and shrink for `LType`.
- [x] Unit tests for `synthesis`.
- [x] quickCheck tests for `synthesis`.
- [x] Unit tests for `checker`.
- [x] quickCheck tests for `checker`.
- [x] Outline function implementation in parser w/ unit tests.
- [x] Outline function implementation in evaluator w/ unit tests.
- [x] Add tests for union types with explicit type signatures.

CP2:
- [x] Augment parser to accept optional type signatures (Harry).
- [x] Change evaluator to ignore type signatures. (Harry)
- [ ] Fix parser to get round-trip propert back (Harry)
- [ ] Modify evaluator to return `ErrorVal` instead of `NilVal`. (Harry)
- [x] Change return type on the type checker functions to be `Either String ()` monad (+ update tests). 
- [ ] Outline abitrary and shrink for well-typed programs. (Wes)
- [ ] Add additional quickCheck property for type checker about well-typed programs. (Wes)
- [ ] Implement arbitrary and shrink for well-typed programs. (Wes)
- [ ] Implement arbitrary and shrink for `LType`. (Harry)
- [x] Modify parser to parse functions with basic types (nil, int, string, boolean). 
- [x] Add more advanced types to the parser (table, functions, unions)
- [x] Modify evaluator to evaluate functions.
- [ ] Extend E2E tests to include type checking step. (Harry)
- [ ] Implement `checker`. 
- [ ] Implement `synthesis`.
- [ ] Require tables to be type annotated in type checker (unsure if necessary) 
- [ ] Implement `typeCheckBlock` and `typeCheckStatement`.

Potential Extensions:
- [ ] Be able to check types within stepper. 
- [ ] Proper lexical scoping for function calls. 
- [ ] User Defined types.
- [ ] Allow optional types in tables and functions. 
- [ ] Other things?

## Questions for Nick 


