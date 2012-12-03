This is a library for typeful constraint programming using two-level types in the style of Tim Sheard's Generic Unification functional pearl. I haven't bothered doing anything to make it remotely presentable or usable yet!

* TwoLevelTerms.hs - the core of the library, this defines typeclasses providing support for two-level types and metavariables. Also defines Fix and Id, the trivial recursive and non-recursive meta-level type constructors.
* MetaTerm.hs - provides meta-level type constructors supporting metavariables.
* ConstraintStore.hs - monad transformers used to build a suitable environment to do constraint programming in. Use one StoreT for each type you'll need metavariables for.
* Unification.hs - Generic(ish) first-order unification ala Sheard, using the MetaTerm type. Ripe for further generalisation!
* Test.hs - Not a proper test suite by any means, more like a part-written Hindley-Milner typechecker using metavariables for both types and type schemes.
