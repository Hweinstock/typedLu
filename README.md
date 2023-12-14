# typedLu
Members:
Harrison Weinstock (harrykw)
John-Wesley Appleton (johnwes) 

## File Overview
- `LuParser.hs`: Parsing for lu. Main additions include parsing functions calls, function definitions, and optional type signatures + union types.  
- `LuEvaluator.hs`: Evaluation for lu. Main additions include throwing errors and handling functions calls/definitions.  
- `LuSyntax.hs`: Define the syntax of the Lu language, as well as helpful type class instances such as generating arbitrary programs and pretty printing.  
- `LuTypes.hs`: Define the types of the typedLu language, as well as helpful helper functions and type class instances. For example, subtyping definition lives here.  
- `LuTypeChecker.hs`: Typechecking for lu. This file includes all of the typechecking logic specific to typechecking.  
- `Context.hs`: Defines `Environment` type class which contains shared logic among typechecker and evaluator (mostly working with state and tracking variables).  
- `Stack.hs`: Custom stack for use of tracking local varaibles. Mostly vanilla, with a few special features.  
- `LuStepper.hs`: Unchanged from HW5. 
- `Parser.hs`: Unchanged from HW5. 

All files have corresponding test files in `/test/` with the addition of `LuE2ETest.hs`. This test file includes the code to run parsing, typechecking, and evaluating on entire programs at once. It also defines a general framework for working with these files such as helpful debugging functions. 

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
- [x] Fix parser to get round-trip propert back (Harry)
- [x] Modify evaluator to return `ErrorVal` instead of `NilVal`. (Harry)
- [x] Change return type on the type checker functions to be `Either String ()` monad (+ update tests). 
- [x] Outline abitrary and shrink for well-typed programs. (Wes)
- [x] Add additional quickCheck property for type checker about well-typed programs. (Wes)
- [x] Implement arbitrary and shrink for well-typed programs. (Wes)
- [x] Implement arbitrary and shrink for `LType`. (Harry)
- [x] Modify parser to parse functions with basic types (nil, int, string, boolean). 
- [x] Add more advanced types to the parser (table, functions, unions)
- [x] Modify evaluator to evaluate functions.
- [x] Extend E2E tests to include type checking step. (Harry)
- [x] Implement `checker`. 
- [x] Implement `synthesis`.
- [x] Implement `typeCheckBlock` and `typeCheckStatement`.
- [x] Generalize store used in evaluator to use `Environment`. (Harry)
- [x] Build some nice demo/ui to show that it works. 

Potential Extensions:
- [ ] Implement Local variables. 
- [ ] Lexical Scoping for functions. 
- [ ] Be able to check types within stepper.  
- [ ] User Defined types.
- [ ] Type assertions / coercions
- [ ] Allow optional types in tables and functions. 
- [ ] Other things?


