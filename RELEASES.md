# Releases

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the [Haskell Package Versioning Policy](https://pvp.haskell.org/).

## [0.2.0] - 2018-10-08

### Added

- Expose instrumentation of data structures as a safe interface in the `IO` monad.
- Add monadic folds and unfolds `translateA`, `foldM`, `unfoldM`, and `unzipWithM` to `Test.StrictCheck.Shaped`.

### Removed

- Remove the referentially opaque observation primitives in `Test.StrictCheck.Unsafe`.

### Changed

- Improve type inference by making `Shape` an injective type family.

## [0.1.1] - 2018-10-01

### Fixed

- Fix critical semantic [bug #2](https://github.com/kwf/StrictCheck/issues/2) which caused violation of referential transparency when compiling with optimizations on GHC 8.6.

## [0.1.0] - 2018-06-22

First release of StrictCheck. This version matches the reviewed artifact submitted to ICFP, archived on the ACM DL, with the exception of some small documentation tweaks.
